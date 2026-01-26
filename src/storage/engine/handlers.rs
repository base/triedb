//! Handler methods for trie modification operations.
//!
//! This module contains the implementation of various trie modification handlers,
//! organized by the type of operation they perform:
//!
//! - **Branch handlers**: Creating and manipulating branch nodes
//! - **Leaf handlers**: Updating account and storage leaf nodes
//! - **Cleanup handlers**: Merging and deleting nodes after modifications

use super::{helpers, Error, PointerChange, StorageEngine};
use crate::{
    context::TransactionContext,
    location::Location,
    node::{Node, TrieValue},
    page::{SlottedPageMut, CELL_POINTER_SIZE},
    path::RawPath,
    pointer::Pointer,
    storage::value::Value,
};
use alloy_trie::Nibbles;

impl StorageEngine {
    // ==================== Branch Handlers ====================

    /// Handles the case when the path does not match the node prefix.
    ///
    /// This creates a new branch node as the parent of the current node,
    /// with children pointing to both the existing node and the new value.
    ///
    /// # Example
    /// If we have a node with prefix "abc" and want to insert at path "abd":
    /// 1. Create new branch with prefix "ab"
    /// 2. Move existing node to be child at index 'c'
    /// 3. Insert new value as child at index 'd'
    pub(super) fn handle_missing_parent_branch(
        &self,
        context: &mut TransactionContext,
        changes: &[(RawPath, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        cell_index: u8,
        node: &mut Node,
        common_prefix: &RawPath,
    ) -> Result<PointerChange, Error> {
        // Create a new branch node with the common prefix
        let mut new_parent_branch = Node::new_branch(common_prefix)?;

        // Ensure page has enough space for a new branch, a new cell pointer for the new branch,
        // while taking into account the space saving from shrinking the existing node's prefix.
        if slotted_page.num_free_bytes() <
            new_parent_branch.size() + CELL_POINTER_SIZE - common_prefix.len() / 2
        {
            self.split_page(context, slotted_page)?;
            return Err(Error::PageSplit(0));
        }
        let node_branch_index = node.prefix().get_unchecked(common_prefix.len());
        // Update the existing node with the new prefix
        node.set_prefix(node.prefix().slice(common_prefix.len() + 1..))?;
        let rlp_node = node.to_rlp_node();
        slotted_page.set_value(cell_index, node)?;

        // Make sure there is no insertions until the new branch node is inserted
        let new_parent_branch_cell_index = slotted_page.next_free_cell_index()?;
        // Set child location to new_parent_branch_cell_index since it will be swapped with the
        // existing node later.
        new_parent_branch.set_child(
            node_branch_index,
            Pointer::new(Location::for_cell(new_parent_branch_cell_index), rlp_node),
        )?;
        let inserted_branch_cell_index = slotted_page.insert_value(&new_parent_branch)?;
        debug_assert_eq!(
            inserted_branch_cell_index, new_parent_branch_cell_index,
            "new parent branch cell index should be the same as the next free cell index, a different caused by interruption between the next_free_cell_index and insert_value"
        );
        slotted_page.swap_cell_pointers(cell_index, new_parent_branch_cell_index)?;

        // Insert the changes into the new branch via recursion
        self.set_values_in_cloned_page(context, changes, path_offset, slotted_page, cell_index)
    }

    /// Handles traversal through a branch node.
    ///
    /// Partitions changes by which child they should go to (based on the next nibble
    /// in their path), then recursively processes each group.
    pub(super) fn handle_branch_node_traversal(
        &self,
        context: &mut TransactionContext,
        changes: &[(RawPath, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &mut Node,
        common_prefix: &RawPath,
    ) -> Result<PointerChange, Error> {
        // Partition changes by child index
        let mut remaining_changes = changes;
        let mut handled_in_children: usize = 0;

        for child_index in 0..16 {
            let matching_changes;
            (matching_changes, remaining_changes) =
                remaining_changes.split_at(remaining_changes.partition_point(|(path, _)| {
                    path.get_unchecked(path_offset as usize + common_prefix.len()) == child_index
                }));

            if matching_changes.is_empty() {
                continue;
            }
            let result = self.handle_child_node_traversal(
                context,
                matching_changes,
                path_offset,
                slotted_page,
                page_index,
                node,
                common_prefix,
                child_index,
            );
            match result {
                Err(Error::PageSplit(processed)) => {
                    return Err(Error::PageSplit(handled_in_children + processed));
                }
                Err(e) => {
                    return Err(e);
                }
                _ => {}
            }
            handled_in_children += matching_changes.len();
        }
        assert!(handled_in_children == changes.len(), "all changes should be handled");

        // Check if the branch node should be deleted or merged
        self.handle_branch_node_cleanup(context, slotted_page, page_index, node)
    }

    /// Handles traversal to a specific child of a branch node.
    fn handle_child_node_traversal(
        &self,
        context: &mut TransactionContext,
        matching_changes: &[(RawPath, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &mut Node,
        common_prefix: &RawPath,
        child_index: u8,
    ) -> Result<(), Error> {
        // Get the child pointer for this index
        let child_pointer = node.child(child_index)?;

        match child_pointer {
            Some(child_pointer) => {
                // Child exists, traverse it
                let child_location = child_pointer.location();
                let child_pointer_change =
                    if let Some(child_cell_index) = child_location.cell_index() {
                        // Local child node
                        self.set_values_in_cloned_page(
                            context,
                            matching_changes,
                            path_offset + common_prefix.len() as u8 + 1,
                            slotted_page,
                            child_cell_index,
                        )?
                    } else {
                        // Remote child node
                        let child_page_id = child_location.page_id().unwrap();
                        self.set_values_in_page(
                            context,
                            matching_changes,
                            path_offset + common_prefix.len() as u8 + 1,
                            child_page_id,
                        )?
                    };

                match child_pointer_change {
                    PointerChange::Update(new_child_pointer) => {
                        self.update_node_child(
                            node,
                            slotted_page,
                            page_index,
                            Some(new_child_pointer),
                            child_index,
                        )?;
                    }
                    PointerChange::Delete => {
                        self.update_node_child(node, slotted_page, page_index, None, child_index)?;
                    }
                    PointerChange::None => {}
                }
            }
            None => {
                // the child node does not exist, so we need to create a new leaf node with the
                // remaining path.

                // in this case, if the change(s) we want to make are deletes, they should be
                // ignored as the child node already doesn't exist.
                let index_of_first_non_delete_change =
                    matching_changes.iter().position(|(_, value)| value.is_some());

                let matching_changes_without_leading_deletes =
                    match index_of_first_non_delete_change {
                        Some(index) => &matching_changes[index..],
                        None => &[],
                    };

                if matching_changes_without_leading_deletes.is_empty() {
                    return Ok(());
                }

                let ((path, value), matching_changes) =
                    matching_changes_without_leading_deletes.split_first().unwrap();
                let remaining_path = path.slice(path_offset as usize + common_prefix.len() + 1..);

                let value = value.as_ref().unwrap();

                // ensure that the page has enough space to insert a new leaf node.
                let node_size_incr = node.size_incr_with_new_child();
                let new_node = Node::new_leaf(&remaining_path, value)?;

                // if the page doesn't have enough space to
                // 1. insert the new leaf node
                // 2. and the node (branch) size increase
                // 3. and add new cell pointer for the new leaf node (3 bytes)
                // when adding the new child, split the page.
                // FIXME: is it safe to split the page here if we've already modified the page?
                if slotted_page.num_free_bytes() <
                    node_size_incr + new_node.size() + CELL_POINTER_SIZE
                {
                    self.split_page(context, slotted_page)?;
                    return Err(Error::PageSplit(0));
                }

                let rlp_node = new_node.to_rlp_node();
                let location = Location::for_cell(slotted_page.insert_value(&new_node)?);
                node.set_child(child_index, Pointer::new(location, rlp_node))?;
                slotted_page.set_value(page_index, node)?;

                // If there are more matching changes, recurse
                if !matching_changes.is_empty() {
                    let child_pointer_change = self.set_values_in_cloned_page(
                        context,
                        matching_changes,
                        path_offset + common_prefix.len() as u8 + 1,
                        slotted_page,
                        location.cell_index().unwrap(),
                    )?;

                    match child_pointer_change {
                        PointerChange::Update(new_child_pointer) => {
                            self.update_node_child(
                                node,
                                slotted_page,
                                page_index,
                                Some(new_child_pointer),
                                child_index,
                            )?;
                        }
                        PointerChange::Delete => {
                            self.update_node_child(
                                node,
                                slotted_page,
                                page_index,
                                None,
                                child_index,
                            )?;
                        }
                        PointerChange::None => {}
                    }
                }
            }
        }
        Ok(())
    }

    /// Handles cleanup of branch nodes (deletion or merging).
    ///
    /// After modifications, a branch node may need cleanup:
    /// - If it has no children, delete it
    /// - If it has exactly one child, merge with that child
    /// - Otherwise, just update its pointer
    pub(super) fn handle_branch_node_cleanup(
        &self,
        context: &mut TransactionContext,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &Node,
    ) -> Result<PointerChange, Error> {
        let children = node.enumerate_children()?;
        if children.is_empty() {
            // Delete empty branch node
            slotted_page.delete_value(page_index)?;
            // If we're the root node, orphan our page
            if page_index == 0 {
                self.orphan_page(context, slotted_page.id())?;
            }
            Ok(PointerChange::Delete)
        } else if children.len() == 1 {
            // Merge branch with its only child
            let (idx, ptr) = children[0];
            self.merge_branch_with_only_child(context, slotted_page, page_index, node, idx, ptr)
        } else {
            // Normal branch node with multiple children
            let rlp_node = node.to_rlp_node();
            Ok(PointerChange::Update(Pointer::new(
                helpers::node_location(slotted_page.id(), page_index),
                rlp_node,
            )))
        }
    }

    /// Merges a branch node with its only child.
    ///
    /// When a branch has only one child remaining, we can merge them by:
    /// 1. Combining their prefixes
    /// 2. Replacing the branch with the child
    fn merge_branch_with_only_child(
        &self,
        context: &mut TransactionContext,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &Node,
        only_child_index: u8,
        only_child_node_pointer: &Pointer,
    ) -> Result<PointerChange, Error> {
        // Compute the prefix to prepend to the child's prefix:
        // parent's prefix + child index
        let mut path_prefix = *node.prefix();
        path_prefix.push(only_child_index);

        if let Some(child_cell_index) = only_child_node_pointer.location().cell_index() {
            // Child is on the same page
            self.merge_with_child_on_same_page(
                slotted_page,
                page_index,
                child_cell_index,
                path_prefix,
            )
        } else {
            // Child is on another page
            let child_page_id =
                only_child_node_pointer.location().page_id().expect("page_id should exist");
            let child_page = self.get_mut_clone(context, child_page_id)?;
            let child_slotted_page = SlottedPageMut::try_from(child_page)?;

            self.merge_with_child_on_different_page(
                context,
                slotted_page,
                page_index,
                child_slotted_page,
                path_prefix,
            )
        }
    }

    /// Handles merging a branch with a child on the same page.
    fn merge_with_child_on_same_page(
        &self,
        slotted_page: &mut SlottedPageMut<'_>,
        parent_cell_index: u8,
        child_cell_index: u8,
        path_prefix: Nibbles,
    ) -> Result<PointerChange, Error> {
        // Read fresh child node and apply merged prefix
        let mut child_node: Node = slotted_page.get_value(child_cell_index)?;
        let merged_prefix = path_prefix.join(child_node.prefix());
        child_node.set_prefix(merged_prefix)?;

        // Compute RLP from the fresh node with merged prefix
        let rlp_node = child_node.to_rlp_node();

        // Delete both nodes and insert the merged one
        slotted_page.delete_value(child_cell_index)?;
        slotted_page.set_value(parent_cell_index, &child_node)?;

        Ok(PointerChange::Update(Pointer::new(
            helpers::node_location(slotted_page.id(), parent_cell_index),
            rlp_node,
        )))
    }

    /// Handles merging a branch with a child on a different page.
    /// Reads fresh child node data to avoid stale child pointers.
    fn merge_with_child_on_different_page(
        &self,
        context: &mut TransactionContext,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        mut child_slotted_page: SlottedPageMut<'_>,
        path_prefix: Nibbles,
    ) -> Result<PointerChange, Error> {
        let branch_page_id = slotted_page.id();

        // Ensure the child page has enough space
        if child_slotted_page.num_free_bytes() < 200 {
            self.split_page(context, &mut child_slotted_page)?;
            // Not returning Error::PageSplit because we're splitting the child page
        }

        // Delete ourselves
        slotted_page.delete_value(page_index)?;

        // Read fresh child node and apply merged prefix
        let mut child_node: Node = child_slotted_page.get_value(0)?;
        let merged_prefix = path_prefix.join(child_node.prefix());
        child_node.set_prefix(merged_prefix)?;

        // Compute RLP from the fresh node with merged prefix
        let rlp_node = child_node.to_rlp_node();

        // Write back the updated node
        child_slotted_page.set_value(0, &child_node)?;

        // If we're the root node, orphan our page
        if page_index == 0 {
            self.orphan_page(context, branch_page_id)?;
        }

        Ok(PointerChange::Update(Pointer::new(
            helpers::node_location(child_slotted_page.id(), 0),
            rlp_node,
        )))
    }

    // ==================== Leaf Handlers ====================

    /// Handles the case when the path matches the node prefix exactly.
    ///
    /// This handles updating or deleting the value at the current node.
    pub(super) fn handle_exact_prefix_match(
        &self,
        context: &mut TransactionContext,
        changes: &[(RawPath, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &mut Node,
        path: RawPath,
        value: Option<&TrieValue>,
    ) -> Result<PointerChange, Error> {
        if value.is_none() {
            // Delete the node
            if node.has_children() {
                // Delete the entire subtrie (e.g., for an AccountLeaf, delete all storage)
                self.delete_subtrie(context, slotted_page, page_index)?;
            }

            slotted_page.delete_value(page_index)?;

            assert_eq!(
                changes.len(),
                1,
                "the node has been deleted from the slotted \
                page and recursively trying to process anymore \
                changes will result in an error"
            );
            return Ok(PointerChange::Delete);
        }

        let (_, remaining_changes) = changes.split_first().unwrap();

        // skip if the value is the same as the current value
        if &node.value()? == value.unwrap() {
            if remaining_changes.is_empty() {
                return Ok(PointerChange::None);
            }

            return self.set_values_in_cloned_page(
                context,
                remaining_changes,
                path_offset,
                slotted_page,
                page_index,
            );
        }

        // Update the node with the new value
        let mut new_node = Node::new_leaf(&path, value.unwrap())?;
        if node.has_children() {
            if let Some(child_pointer) = node.direct_child()? {
                new_node.set_child(0, child_pointer.clone())?;
            }
        }

        let old_node_size = node.size();
        let new_node_size = new_node.size();
        if new_node_size > old_node_size {
            let node_size_incr = new_node_size - old_node_size;
            if slotted_page.num_free_bytes() < node_size_incr {
                self.split_page(context, slotted_page)?;
                return Err(Error::PageSplit(0));
            }
        }

        slotted_page.set_value(page_index, &new_node)?;

        if remaining_changes.is_empty() {
            let rlp_node = new_node.to_rlp_node();
            Ok(PointerChange::Update(Pointer::new(
                helpers::node_location(slotted_page.id(), page_index),
                rlp_node,
            )))
        } else {
            // Recurse with remaining changes - this should return a change to the pointer of the
            // current account node, if any
            let account_pointer_change = self.set_values_in_cloned_page(
                context,
                remaining_changes,
                path_offset,
                slotted_page,
                page_index,
            );
            match account_pointer_change {
                Ok(PointerChange::Update(pointer)) => Ok(PointerChange::Update(pointer)),
                Ok(PointerChange::None) => {
                    // even if the storage is unchanged, we still need to update the RLP encoding of
                    // this account node as its contents have changed
                    let rlp_node = new_node.to_rlp_node();
                    Ok(PointerChange::Update(Pointer::new(
                        helpers::node_location(slotted_page.id(), page_index),
                        rlp_node,
                    )))
                }
                Ok(PointerChange::Delete) => {
                    panic!("unexpected case - account pointer is deleted after update");
                }
                Err(e) => Err(e),
            }
        }
    }

    /// Handles traversal through an account leaf node with a child pointer.
    ///
    /// This is used when we're accessing storage for an account - we need to
    /// traverse into the account's storage trie.
    pub(super) fn handle_account_node_traversal(
        &self,
        context: &mut TransactionContext,
        changes: &[(RawPath, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &mut Node,
        common_prefix: &RawPath,
    ) -> Result<PointerChange, Error> {
        let child_pointer = node.direct_child()?;

        if let Some(child_pointer) = child_pointer {
            let child_pointer_change =
                if let Some(child_cell_index) = child_pointer.location().cell_index() {
                    // Handle local child node (on same page)
                    self.set_values_in_cloned_page(
                        context,
                        changes,
                        path_offset + common_prefix.len() as u8,
                        slotted_page,
                        child_cell_index,
                    )?
                } else {
                    // Handle remote child node (on different page)
                    let child_page_id = child_pointer.location().page_id().unwrap();
                    self.set_values_in_page(
                        context,
                        changes,
                        path_offset + common_prefix.len() as u8,
                        child_page_id,
                    )?
                };

            match child_pointer_change {
                PointerChange::Update(new_child_pointer) => {
                    self.update_node_child(
                        node,
                        slotted_page,
                        page_index,
                        Some(new_child_pointer),
                        0,
                    )?;
                    let rlp_node = node.to_rlp_node();
                    Ok(PointerChange::Update(Pointer::new(
                        helpers::node_location(slotted_page.id(), page_index),
                        rlp_node,
                    )))
                }
                PointerChange::Delete => {
                    self.update_node_child(node, slotted_page, page_index, None, 0)?;
                    let rlp_node = node.to_rlp_node();
                    Ok(PointerChange::Update(Pointer::new(
                        helpers::node_location(slotted_page.id(), page_index),
                        rlp_node,
                    )))
                }
                PointerChange::None => Ok(PointerChange::None),
            }
        } else {
            // The account has no storage trie yet, create a new leaf node for the first slot
            self.create_first_storage_node(
                context,
                changes,
                path_offset,
                slotted_page,
                page_index,
                node,
                common_prefix,
            )
        }
    }

    /// Creates the first storage node for an account.
    ///
    /// This is called when an account has no storage trie yet and we need to
    /// create the first storage slot.
    fn create_first_storage_node(
        &self,
        context: &mut TransactionContext,
        changes: &[(RawPath, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &mut Node,
        common_prefix: &RawPath,
    ) -> Result<PointerChange, Error> {
        if changes.is_empty() {
            return Ok(PointerChange::None);
        }

        // the account has no storage trie yet, so we need to create a new leaf node for the first
        // slot Get the first change and create a new leaf node
        let ((path, value), remaining_changes) = changes.split_first().unwrap();
        if value.is_none() {
            // this is a delete on a storage value that doesn't exist. skip it.
            return self.set_values_in_cloned_page(
                context,
                remaining_changes,
                path_offset,
                slotted_page,
                page_index,
            );
        }

        let node_size_incr = node.size_incr_with_new_child();
        let remaining_path = path.slice(path_offset as usize + common_prefix.len()..);
        let new_node = Node::new_leaf(&remaining_path, value.as_ref().unwrap())?;

        // if the page doesn't have enough space to
        // 1. insert the new leaf node
        // 2. and the node (branch) size increase
        // 3. and add new cell pointer for the new leaf node (3 bytes)
        // when adding the new child, split the page.
        if slotted_page.num_free_bytes() < node_size_incr + new_node.size() + CELL_POINTER_SIZE {
            self.split_page(context, slotted_page)?;
            return Err(Error::PageSplit(0));
        }

        let rlp_node = new_node.to_rlp_node();

        // Insert the new node and update the parent
        let location = Location::for_cell(slotted_page.insert_value(&new_node)?);
        node.set_child(0, Pointer::new(location, rlp_node))?;
        slotted_page.set_value(page_index, node)?;

        if remaining_changes.is_empty() {
            let rlp_node = node.to_rlp_node();
            return Ok(PointerChange::Update(Pointer::new(
                helpers::node_location(slotted_page.id(), page_index),
                rlp_node,
            )));
        }

        // Recurse with the remaining changes
        self.set_values_in_cloned_page(
            context,
            remaining_changes,
            path_offset,
            slotted_page,
            page_index,
        )
    }

    /// Updates a node's child pointer, handling both setting and removal.
    pub(super) fn update_node_child(
        &self,
        node: &mut Node,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        new_child_pointer: Option<Pointer>,
        child_index: u8,
    ) -> Result<(), Error> {
        if let Some(new_child_pointer) = new_child_pointer {
            node.set_child(child_index, new_child_pointer)?;
        } else {
            node.remove_child(child_index)?;
        }

        slotted_page.set_value(page_index, node)?;
        Ok(())
    }
}
