//! Write operations for the storage engine.
//!
//! This module contains the core trie modification logic including:
//! - Setting values (accounts and storage)
//! - Navigating the trie structure during writes
//! - Handling page splits during modifications

use super::{helpers, Error, PointerChange, StorageEngine};
use crate::{
    context::TransactionContext,
    location::Location,
    node::{Node, TrieValue},
    page::{PageError, PageId, SlottedPageMut},
    path::{AddressPath, RawPath, ADDRESS_PATH_LENGTH, STORAGE_PATH_LENGTH},
    pointer::Pointer,
};
use alloy_trie::EMPTY_ROOT_HASH;

impl StorageEngine {
    /// Applies a set of changes to the trie.
    ///
    /// This is the main entry point for modifying trie state. It handles:
    /// - Empty trie initialization
    /// - Cache invalidation for affected storage paths
    /// - Delegating to page-level modification logic
    ///
    /// # Parameters
    /// - `context`: Transaction context for the operation
    /// - `changes`: Mutable slice of (path, value) pairs. Values of None indicate deletion. The
    ///   slice will be sorted by path during processing.
    pub fn set_values(
        &self,
        context: &mut TransactionContext,
        mut changes: &mut [(RawPath, Option<TrieValue>)],
    ) -> Result<(), Error> {
        changes.sort_by(|a, b| a.0.cmp(&b.0));
        if context.root_node_page_id.is_none() {
            // Handle empty trie case, inserting the first new value before traversing the trie.
            let page = self.allocate_page(context)?;
            let mut slotted_page = SlottedPageMut::try_from(page)?;
            let ((path, value), remaining_changes) = changes.split_first_mut().unwrap();
            let value = value.as_ref().expect("unable to delete from empty trie");
            let root_pointer =
                self.initialize_empty_trie(context, path, value, &mut slotted_page)?;
            context.root_node_page_id = root_pointer.location().page_id();
            context.root_node_hash = root_pointer.rlp().as_hash().unwrap();
            if remaining_changes.is_empty() {
                return Ok(());
            }
            changes = remaining_changes;
        }
        // invalidate the cache
        changes.iter().for_each(|(path, _)| {
            if path.len() == STORAGE_PATH_LENGTH {
                let address_path =
                    AddressPath::new(path.slice(..ADDRESS_PATH_LENGTH).try_into().unwrap());
                context.contract_account_loc_cache.remove(&address_path.into());
            }
        });

        let pointer_change =
            self.set_values_in_page(context, changes, 0, context.root_node_page_id.unwrap())?;
        match pointer_change {
            PointerChange::Update(pointer) => {
                context.root_node_page_id = pointer.location().page_id();
                context.root_node_hash = pointer.rlp().as_hash().unwrap();
            }
            PointerChange::Delete => {
                context.root_node_page_id = None;
                context.root_node_hash = EMPTY_ROOT_HASH;
            }
            PointerChange::None => (),
        }
        Ok(())
    }

    /// Applies changes to a specific page, handling page cloning and split retries.
    ///
    /// This function clones the page (copy-on-write) and attempts to apply changes.
    /// If a page split is needed, it retries the operation from scratch.
    pub(super) fn set_values_in_page(
        &self,
        context: &mut TransactionContext,
        mut changes: &[(RawPath, Option<TrieValue>)],
        path_offset: u8,
        page_id: PageId,
    ) -> Result<PointerChange, Error> {
        let page = self.get_mut_clone(context, page_id)?;
        let mut new_slotted_page = SlottedPageMut::try_from(page)?;
        let mut split_count = 0;

        loop {
            let result = self.set_values_in_cloned_page(
                context,
                changes,
                path_offset,
                &mut new_slotted_page,
                0,
            );

            match result {
                Ok(PointerChange::Delete) => return Ok(PointerChange::Delete),
                Ok(PointerChange::None) => return Ok(PointerChange::None),
                Ok(PointerChange::Update(pointer)) => return Ok(PointerChange::Update(pointer)),
                // In the case of a page split, re-attempt the operation from scratch. This ensures
                // that a page will be consistently evaluated, and not modified in
                // the middle of an operation, which could result in inconsistent
                // cell pointers.
                Err(Error::PageSplit(handled_total)) => {
                    changes = &changes[handled_total..];
                    context.transaction_metrics.inc_pages_split();
                    split_count += 1;
                    // FIXME: this is a temporary limit to prevent infinite loops.
                    if split_count > 20 {
                        return Err(Error::PageError(PageError::PageSplitLimitReached));
                    }
                }
                Err(Error::PageError(PageError::PageIsFull)) => {
                    return Err(Error::PageError(PageError::PageIsFull));
                }
                Err(e) => return Err(e),
            }
        }
    }

    /// Applies a set of changes to a cloned page in the trie.
    ///
    /// This method is the core of the trie modification logic. It handles four main cases:
    ///
    /// ## Case 1: Path diverges from node prefix
    /// The path does not match the node prefix (common_prefix < node.prefix).
    /// Creates a new branch node as the parent of the current node, unless we're
    /// deleting (in which case we skip since we don't expand nodes into branches
    /// when removing values).
    ///
    /// ## Case 2: Exact prefix match
    /// The path matches the node prefix exactly (common_prefix == path.len()).
    /// Updates or deletes the value at this node.
    ///
    /// ## Case 3: Account leaf with storage
    /// The node is an AccountLeaf and we need to traverse into its storage trie.
    /// This handles setting/getting storage values for an account.
    ///
    /// ## Case 4: Branch node traversal
    /// The node is a Branch and we need to traverse to the appropriate child
    /// based on the next nibble in the path.
    ///
    /// # Parameters
    /// - `context`: Transaction context for the operation
    /// - `changes`: List of key-value pairs to apply (None value means delete)
    /// - `path_offset`: Current offset into the path being processed. All `changes` must have the
    ///   same prefix up to this point.
    /// - `slotted_page`: The page being modified
    /// - `page_index`: Index of the current node in the page
    ///
    /// # Returns
    /// - `Ok(PointerChange::Update(ptr))`: Pointer to the modified node
    /// - `Ok(PointerChange::Delete)`: Node was deleted
    /// - `Ok(PointerChange::None)`: No changes were needed
    /// - `Err(Error::PageSplit(n))`: Page split occurred after processing n changes
    pub(super) fn set_values_in_cloned_page(
        &self,
        context: &mut TransactionContext,
        changes: &[(RawPath, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
    ) -> Result<PointerChange, Error> {
        if changes.is_empty() {
            return Ok(PointerChange::None);
        }

        let mut node = slotted_page.get_value::<Node>(page_index)?;

        // Find the shortest common prefix between the node path and the changes
        let (shortest_common_prefix_idx, common_prefix_length) =
            helpers::find_shortest_common_prefix(changes, path_offset, &node);

        let first_change = &changes[shortest_common_prefix_idx];
        let path = first_change.0.slice(path_offset as usize..);
        let value = first_change.1.as_ref();
        let common_prefix = path.slice(0..common_prefix_length);

        // Case 1: The path does not match the node prefix, create a new branch node as the parent
        // of the current node except when deleting as we don't want to expand nodes into branches
        // when removing values.
        if common_prefix.len() < node.prefix().len() {
            if value.is_none() {
                let (changes_left, changes_right) = changes.split_at(shortest_common_prefix_idx);
                let changes_right = &changes_right[1..];
                if changes_right.is_empty() {
                    return self.set_values_in_cloned_page(
                        context,
                        changes_left,
                        path_offset,
                        slotted_page,
                        page_index,
                    );
                } else if changes_left.is_empty() {
                    return self.set_values_in_cloned_page(
                        context,
                        changes_right,
                        path_offset,
                        slotted_page,
                        page_index,
                    );
                } else {
                    unreachable!(
                        "shortest_common_prefix_idx is not at either end of the changes array"
                    );
                }
            }
            return self.handle_missing_parent_branch(
                context,
                changes,
                path_offset,
                slotted_page,
                page_index,
                &mut node,
                &common_prefix,
            );
        }

        // Case 2: The path matches the node prefix exactly, update or delete the value
        if common_prefix.len() == path.len() {
            assert_eq!(shortest_common_prefix_idx, 0, "the leftmost change must have the matching prefix, as all other matching changes must be storage descendants of this account");

            return self.handle_exact_prefix_match(
                context,
                changes,
                path_offset,
                slotted_page,
                page_index,
                &mut node,
                path,
                value,
            );
        }

        // Case 3: Handle leaf node with child pointer (e.g., AccountLeaf with storage)
        if node.is_account_leaf() {
            return self.handle_account_node_traversal(
                context,
                changes,
                path_offset,
                slotted_page,
                page_index,
                &mut node,
                &common_prefix,
            );
        }

        // Case 4: Handle branch node traversal
        assert!(node.is_branch(), "node must be a branch at this point");
        self.handle_branch_node_traversal(
            context,
            changes,
            path_offset,
            slotted_page,
            page_index,
            &mut node,
            &common_prefix,
        )
    }

    /// Handles the case when the trie is empty and we need to insert the first node.
    pub(super) fn initialize_empty_trie(
        &self,
        _context: &mut TransactionContext,
        path: &RawPath,
        value: &TrieValue,
        slotted_page: &mut SlottedPageMut<'_>,
    ) -> Result<Pointer, Error> {
        let new_node = Node::new_leaf(path, value)?;
        let rlp_node = new_node.to_rlp_node();

        let index = slotted_page.insert_value(&new_node)?;
        assert_eq!(index, 0, "root node must be at index 0");

        Ok(Pointer::new(Location::for_page(slotted_page.id()), rlp_node))
    }
}
