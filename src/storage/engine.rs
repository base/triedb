use crate::{
    account::Account,
    context::TransactionContext,
    location::Location,
    meta::MetadataManager,
    node::{
        Node,
        Node::{AccountLeaf, Branch},
        NodeError, TrieValue,
    },
    page::{
        Page, PageError, PageId, PageManager, PageMut, SlottedPage, SlottedPageMut,
        CELL_POINTER_SIZE,
    },
    path::{AddressPath, StoragePath, ADDRESS_PATH_LENGTH, STORAGE_PATH_LENGTH},
    pointer::Pointer,
    snapshot::SnapshotId,
    storage::{debug::DebugPage, value::Value},
};
use alloy_primitives::StorageValue;
use alloy_trie::{nodes::RlpNode, nybbles, Nibbles, EMPTY_ROOT_HASH};
use std::{cmp::Ordering, fmt::Debug, io, collections::HashSet};


/// The [StorageEngine] is responsible for managing the storage of data in the database.
/// It handles reading and writing account and storage values, as well as managing the lifecycle of
/// pages.
///
/// The storage engine uses a [PageManager] (`P`) to interact with the underlying storage medium,
/// which could be memory-mapped files, in-memory storage, or other implementations.
#[derive(Debug)]
pub struct StorageEngine {
    page_manager: PageManager,
    meta_manager: MetadataManager,
    alive_snapshot_id: SnapshotId,
}

enum PointerChange {
    None,
    Update(Pointer),
    Delete,
}

impl StorageEngine {
    pub fn new(page_manager: PageManager, meta_manager: MetadataManager) -> Self {
        let alive_snapshot_id = meta_manager.active_slot().snapshot_id();
        Self { page_manager, meta_manager, alive_snapshot_id }
    }

    pub fn metadata(&self) -> &MetadataManager {
        &self.meta_manager
    }

    /// Returns a [`TransactionContext`] valid for reads.
    ///
    /// The returned context points to the latest committed snapshot.
    pub(crate) fn read_context(&self) -> TransactionContext {
        let meta = self.meta_manager.active_slot();
        TransactionContext::new(meta)
    }

    /// Returns a [`TransactionContext`] valid for writes
    ///
    /// The returned context points to the latest uncommitted snapshot.
    pub(crate) fn write_context(&self) -> TransactionContext {
        let meta = self.meta_manager.dirty_slot();
        TransactionContext::new(meta)
    }

    /// Unlocks any orphaned pages as of the given [SnapshotId] for reuse.
    pub(crate) fn unlock(&mut self, snapshot_id: SnapshotId) {
        self.alive_snapshot_id = snapshot_id + 1;
    }

    /// Retrieves a mutable clone of a [Page] from the underlying [PageManager].
    /// The original page is marked as orphaned and a new page is allocated, potentially from an
    /// orphaned page.
    fn get_mut_clone<'p>(
        &mut self,
        context: &mut TransactionContext,
        page_id: PageId,
    ) -> Result<PageMut<'p>, Error> {
        let original_page = self.get_mut_page(context, page_id)?;

        // if the page already has the correct snapshot id, return it without cloning.
        if original_page.snapshot_id() == context.snapshot_id {
            return Ok(original_page);
        }

        let mut new_page = self.allocate_page(context)?;

        self.meta_manager.orphan_pages().push(page_id)?;
        new_page.contents_mut().copy_from_slice(original_page.contents());
        Ok(new_page)
    }

    /// Retrieves a read-only [SlottedPage] from the underlying [PageManager].
    pub(crate) fn get_slotted_page<'p>(
        &self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<SlottedPage<'p>, Error> {
        let page = self.get_page(context, page_id)?;
        Ok(SlottedPage::try_from(page)?)
    }

    /// Retrieves an [Account] from the storage engine, identified by the given [AddressPath].
    /// Returns [None] if the path is not found.
    pub fn get_account(
        &self,
        context: &mut TransactionContext,
        address_path: AddressPath,
    ) -> Result<Option<Account>, Error> {
        match context.root_node_page_id {
            None => Ok(None),
            Some(root_node_page_id) => {
                let page = self.get_page(context, root_node_page_id)?;
                let slotted_page = SlottedPage::try_from(page)?;
                let path: Nibbles = address_path.into();

                match self.get_value_from_page(context, &path, 0, slotted_page, 0)? {
                    Some(TrieValue::Account(account)) => Ok(Some(account)),
                    _ => Ok(None),
                }
            }
        }
    }

    /// Retrieves a [StorageValue] from the storage engine, identified by the given [StoragePath].
    /// Returns [None] if the path is not found.
    pub fn get_storage(
        &self,
        context: &mut TransactionContext,
        storage_path: StoragePath,
    ) -> Result<Option<StorageValue>, Error> {
        let root_node_page_id = match context.root_node_page_id {
            None => return Ok(None),
            Some(page_id) => page_id,
        };

        let original_path: Nibbles = storage_path.full_path();

        // check the cache
        let nibbles = storage_path.get_address().to_nibbles();
        let cache_location = context.contract_account_loc_cache.get(nibbles);
        let (slotted_page, page_index, path_offset) = match cache_location {
            Some((page_id, page_index)) => {
                context.transaction_metrics.inc_cache_storage_read_hit();

                let path_offset = storage_path.get_slot_offset();
                // read the current account
                let page = self.get_page(context, page_id)?;
                let slotted_page = SlottedPage::try_from(page)?;
                let node: Node = slotted_page.get_value(page_index)?;
                let child_pointer = node.direct_child()?;
                // only when the node is an account leaf and all storage slots are removed
                if child_pointer.is_none() {
                    return Ok(None);
                }
                let child_location = child_pointer.unwrap().location();
                let (slotted_page, page_index) = if child_location.cell_index().is_some() {
                    (slotted_page, child_location.cell_index().unwrap())
                } else {
                    let child_page_id = child_location.page_id().unwrap();
                    let child_page = self.get_page(context, child_page_id)?;
                    let child_slotted_page = SlottedPage::try_from(child_page)?;
                    (child_slotted_page, 0)
                };
                (slotted_page, page_index, path_offset)
            }
            None => {
                context.transaction_metrics.inc_cache_storage_read_miss();

                let page = self.get_page(context, root_node_page_id)?;
                let slotted_page = SlottedPage::try_from(page)?;
                (slotted_page, 0, 0)
            }
        };

        match self.get_value_from_page(
            context,
            &original_path,
            path_offset,
            slotted_page,
            page_index,
        )? {
            Some(TrieValue::Storage(storage_value)) => Ok(Some(storage_value)),
            _ => Ok(None),
        }
    }

    /// Retrieves a [TrieValue] from the given page or any of its descendants.
    /// Returns [None] if the path is not found.
    fn get_value_from_page(
        &self,
        context: &mut TransactionContext,
        original_path_slice: &[u8],
        path_offset: usize,
        slotted_page: SlottedPage<'_>,
        page_index: u8,
    ) -> Result<Option<TrieValue>, Error> {
        let node: Node = slotted_page.get_value(page_index)?;

        let common_prefix_length =
            nybbles::common_prefix_length(&original_path_slice[path_offset..], node.prefix());

        if common_prefix_length < node.prefix().len() {
            return Ok(None);
        }

        let remaining_path = &original_path_slice[path_offset + common_prefix_length..];
        if remaining_path.is_empty() {
            // cache the account location if it is a contract account
            if let TrieValue::Account(account) = node.value()? {
                if account.storage_root != EMPTY_ROOT_HASH &&
                    original_path_slice.len() == ADDRESS_PATH_LENGTH
                {
                    let original_path = Nibbles::from_nibbles_unchecked(original_path_slice);
                    context
                        .contract_account_loc_cache
                        .insert(&original_path, (slotted_page.id(), page_index));
                }
            }

            return Ok(Some(node.value()?));
        }

        let (child_pointer, new_path_offset) = match node {
            AccountLeaf { ref storage_root, .. } => {
                (storage_root.as_ref(), path_offset + common_prefix_length)
            }
            Branch { ref children, .. } => (
                children[remaining_path[0] as usize].as_ref(),
                path_offset + common_prefix_length + 1,
            ),
            _ => unreachable!(),
        };

        match child_pointer {
            Some(child_pointer) => {
                let child_location = child_pointer.location();
                if child_location.cell_index().is_some() {
                    self.get_value_from_page(
                        context,
                        original_path_slice,
                        new_path_offset,
                        slotted_page,
                        child_location.cell_index().unwrap(),
                    )
                } else {
                    let child_page_id = child_location.page_id().unwrap();
                    let child_page = self.get_page(context, child_page_id)?;
                    let child_slotted_page = SlottedPage::try_from(child_page)?;
                    self.get_value_from_page(
                        context,
                        original_path_slice,
                        new_path_offset,
                        child_slotted_page,
                        0,
                    )
                }
            }
            None => Ok(None),
        }
    }

    pub fn set_values(
        &mut self,
        context: &mut TransactionContext,
        mut changes: &mut [(Nibbles, Option<TrieValue>)],
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
                let address_path = AddressPath::new(path.slice(0..ADDRESS_PATH_LENGTH));
                context.contract_account_loc_cache.remove(address_path.to_nibbles());
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

    fn set_values_in_page(
        &mut self,
        context: &mut TransactionContext,
        mut changes: &[(Nibbles, Option<TrieValue>)],
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
                // This case means the root node was deleted so orphan this page.
                // TODO: this page could actually be reallocated in the same transaction,
                // but this would require adding the page_id to a pending buffer. It would
                // still be orphaned if unused by the end of the transaction.
                Ok(PointerChange::Delete) => {
                    self.meta_manager.orphan_pages().push(page_id)?;
                    return Ok(PointerChange::Delete);
                }
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
    /// This method is the core of the trie modification logic. It handles:
    /// - Creating new nodes when the trie is empty
    /// - Updating existing nodes with new values
    /// - Creating branch nodes when paths diverge
    /// - Deleting nodes and cleaning up the trie structure
    /// - Merging nodes when a branch has only one child
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
    /// - `Ok(Some(Pointer))`: Pointer to the modified node
    /// - `Ok(None)`: Node was deleted
    /// - `Err(Error)`: Operation failed, possibly due to page split
    fn set_values_in_cloned_page(
        &mut self,
        context: &mut TransactionContext,
        changes: &[(Nibbles, Option<TrieValue>)],
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
            find_shortest_common_prefix(changes, path_offset, &node);

        let first_change = &changes[shortest_common_prefix_idx];
        let path = first_change.0.slice(path_offset as usize..);
        let value = first_change.1.as_ref();
        let common_prefix = path.slice(0..common_prefix_length);

        // Case 1: The path does not match the node prefix, create a new branch node as the parent
        // of the current node except when deleting as we don't want to expand nodes into branches
        // when removing values.
        if common_prefix_length < node.prefix().len() {
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
                common_prefix,
                common_prefix_length,
            );
        }

        // Case 2: The path matches the node prefix exactly, update or delete the value
        if common_prefix_length == path.len() {
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
                common_prefix_length,
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
            common_prefix_length,
        )
    }

    /// Handles the case when the trie is empty and we need to insert the first node
    fn initialize_empty_trie(
        &self,
        _context: &mut TransactionContext,
        path: &Nibbles,
        value: &TrieValue,
        slotted_page: &mut SlottedPageMut<'_>,
    ) -> Result<Pointer, Error> {
        let new_node = Node::new_leaf(path.clone(), value)?;
        let rlp_node = new_node.as_rlp_node();

        let index = slotted_page.insert_value(&new_node)?;
        assert_eq!(index, 0, "root node must be at index 0");

        Ok(Pointer::new(Location::for_page(slotted_page.id()), rlp_node))
    }

    /// Handles the case when the path does not match the node prefix
    fn handle_missing_parent_branch(
        &mut self,
        context: &mut TransactionContext,
        changes: &[(Nibbles, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &mut Node,
        common_prefix: Nibbles,
        common_prefix_length: usize,
    ) -> Result<PointerChange, Error> {
        // Create a new branch node with the common prefix
        let mut new_parent_branch = Node::new_branch(common_prefix)?;

        // Ensure page has enough space for a new branch + a new leaf node.
        // a. New leaf node created in next free cell index.
        // b. New branch node created by updating the existing node at page_index. Usually the
        // branch node with 2 children size is (2+2+2*37 = 78 bytes) + prefix_length, the account
        // node (not contract) is smaller, hence will delete the current cell and allocate new cell.
        //
        // Another approach could be more efficient to consider:
        // a. Update current cell with new node (smaller size since the prefix is shorter), create
        // new pointer to this cell.
        // b. Create a new cell for the new branch node. Update page_index to point to this new
        // branch.
        //
        // This approach allocate only 1 new slotted page for the branch node.
        if slotted_page.num_free_bytes() < node.size() + new_parent_branch.size() {
            self.split_page(context, slotted_page)?;
            return Err(Error::PageSplit(0));
        }

        // Update the prefix of the existing node and insert it into the page
        let node_branch_index = node.prefix()[common_prefix_length];
        node.set_prefix(node.prefix().slice(common_prefix_length + 1..))?;
        let rlp_node = node.as_rlp_node();
        let location = Location::for_cell(slotted_page.insert_value(node)?);
        new_parent_branch.set_child(node_branch_index, Pointer::new(location, rlp_node))?;

        // Set the new branch as the current node
        slotted_page.set_value(page_index, &new_parent_branch)?;

        // Insert the changes into the new branch via recursion
        self.set_values_in_cloned_page(context, changes, path_offset, slotted_page, page_index)
    }

    /// Handles the case when the path matches the node prefix exactly
    fn handle_exact_prefix_match(
        &mut self,
        context: &mut TransactionContext,
        changes: &[(Nibbles, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &mut Node,
        path: Nibbles,
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
        let mut new_node = Node::new_leaf(path, value.unwrap())?;
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
            let rlp_node = new_node.as_rlp_node();
            Ok(PointerChange::Update(Pointer::new(
                node_location(slotted_page.id(), page_index),
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
                    let rlp_node = new_node.as_rlp_node();
                    Ok(PointerChange::Update(Pointer::new(
                        node_location(slotted_page.id(), page_index),
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

    /// Handles traversal through an account leaf node with a child pointer
    fn handle_account_node_traversal(
        &mut self,
        context: &mut TransactionContext,
        changes: &[(Nibbles, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &mut Node,
        common_prefix_length: usize,
    ) -> Result<PointerChange, Error> {
        let child_pointer = node.direct_child()?;

        if let Some(child_pointer) = child_pointer {
            let child_pointer_change =
                if let Some(child_cell_index) = child_pointer.location().cell_index() {
                    // Handle local child node (on same page)
                    self.set_values_in_cloned_page(
                        context,
                        changes,
                        path_offset + common_prefix_length as u8,
                        slotted_page,
                        child_cell_index,
                    )?
                } else {
                    // Handle remote child node (on different page)
                    let child_page_id = child_pointer.location().page_id().unwrap();
                    self.set_values_in_page(
                        context,
                        changes,
                        path_offset + common_prefix_length as u8,
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
                    let rlp_node = node.as_rlp_node();
                    Ok(PointerChange::Update(Pointer::new(
                        node_location(slotted_page.id(), page_index),
                        rlp_node,
                    )))
                }
                PointerChange::Delete => {
                    self.update_node_child(node, slotted_page, page_index, None, 0)?;
                    let rlp_node = node.as_rlp_node();
                    Ok(PointerChange::Update(Pointer::new(
                        node_location(slotted_page.id(), page_index),
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
                common_prefix_length,
            )
        }
    }

    /// Creates the first storage node for an account
    fn create_first_storage_node(
        &mut self,
        context: &mut TransactionContext,
        changes: &[(Nibbles, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &mut Node,
        common_prefix_length: usize,
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
        let remaining_path = path.slice(path_offset as usize + common_prefix_length..);
        let new_node = Node::new_leaf(remaining_path, value.as_ref().unwrap())?;

        // if the page doesn't have enough space to
        // 1. insert the new leaf node
        // 2. and the node (branch) size increase
        // 3. and add new cell pointer for the new leaf node (3 bytes)
        // when adding the new child, split the page.
        if slotted_page.num_free_bytes() < node_size_incr + new_node.size() + CELL_POINTER_SIZE {
            self.split_page(context, slotted_page)?;
            return Err(Error::PageSplit(0));
        }

        let rlp_node = new_node.as_rlp_node();

        // Insert the new node and update the parent
        let location = Location::for_cell(slotted_page.insert_value(&new_node)?);
        node.set_child(0, Pointer::new(location, rlp_node))?;
        slotted_page.set_value(page_index, node)?;

        if remaining_changes.is_empty() {
            let rlp_node = node.as_rlp_node();
            return Ok(PointerChange::Update(Pointer::new(
                node_location(slotted_page.id(), page_index),
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

    /// Updates a node's child pointer, handling both setting and removal
    fn update_node_child(
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

    /// Handles traversal through a branch node
    fn handle_branch_node_traversal(
        &mut self,
        context: &mut TransactionContext,
        changes: &[(Nibbles, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &mut Node,
        common_prefix_length: usize,
    ) -> Result<PointerChange, Error> {
        // Partition changes by child index
        let mut remaining_changes = changes;
        let mut handled_in_children: usize = 0;

        for child_index in 0..16 {
            let matching_changes;
            (matching_changes, remaining_changes) =
                remaining_changes.split_at(remaining_changes.partition_point(|(path, _)| {
                    path[path_offset as usize + common_prefix_length] == child_index
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
                common_prefix_length,
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

    fn handle_child_node_traversal(
        &mut self,
        context: &mut TransactionContext,
        matching_changes: &[(Nibbles, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &mut Node,
        common_prefix_length: usize,
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
                            path_offset + common_prefix_length as u8 + 1,
                            slotted_page,
                            child_cell_index,
                        )?
                    } else {
                        // Remote child node
                        let child_page_id = child_location.page_id().unwrap();
                        self.set_values_in_page(
                            context,
                            matching_changes,
                            path_offset + common_prefix_length as u8 + 1,
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
                let remaining_path: Nibbles =
                    path.slice(path_offset as usize + common_prefix_length + 1..);

                let value = value.as_ref().unwrap();

                // ensure that the page has enough space to insert a new leaf node.
                let node_size_incr = node.size_incr_with_new_child();
                let new_node = Node::new_leaf(remaining_path, value)?;

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

                let rlp_node = new_node.as_rlp_node();
                let location = Location::for_cell(slotted_page.insert_value(&new_node)?);
                node.set_child(child_index, Pointer::new(location, rlp_node))?;
                slotted_page.set_value(page_index, node)?;

                // If there are more matching changes, recurse
                if !matching_changes.is_empty() {
                    let child_pointer_change = self.set_values_in_cloned_page(
                        context,
                        matching_changes,
                        path_offset + common_prefix_length as u8 + 1,
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

    /// Handles cleanup of branch nodes (deletion or merging)
    fn handle_branch_node_cleanup(
        &mut self,
        context: &mut TransactionContext,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &Node,
    ) -> Result<PointerChange, Error> {
        let children = node.enumerate_children()?;
        if children.is_empty() {
            // Delete empty branch node
            slotted_page.delete_value(page_index)?;
            Ok(PointerChange::Delete)
        } else if children.len() == 1 {
            // Merge branch with its only child
            let (idx, ptr) = children[0];
            return self.merge_branch_with_only_child(
                context,
                slotted_page,
                page_index,
                node,
                idx,
                ptr,
            );
        } else {
            // Normal branch node with multiple children
            let rlp_node = node.as_rlp_node();
            return Ok(PointerChange::Update(Pointer::new(
                node_location(slotted_page.id(), page_index),
                rlp_node,
            )));
        }
    }

    /// Merges a branch node with its only child
    fn merge_branch_with_only_child(
        &mut self,
        context: &mut TransactionContext,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        node: &Node,
        only_child_index: u8,
        only_child_node_pointer: &Pointer,
    ) -> Result<PointerChange, Error> {
        // Get the child node
        let (mut only_child_node, child_slotted_page) =
            if let Some(cell_index) = only_child_node_pointer.location().cell_index() {
                // Child is on the same page
                (slotted_page.get_value::<Node>(cell_index)?, None)
            } else {
                // Child is on another page
                let child_page = self.get_mut_clone(
                    context,
                    only_child_node_pointer.location().page_id().expect("page_id should exist"),
                )?;
                let child_slotted_page = SlottedPageMut::try_from(child_page)?;
                (child_slotted_page.get_value(0)?, Some(child_slotted_page))
            };

        // Create the new merged prefix
        let mut new_nibbles = node.prefix().clone();
        new_nibbles.push(only_child_index);
        new_nibbles = new_nibbles.join(only_child_node.prefix());
        only_child_node.set_prefix(new_nibbles)?;

        // Get the RLP node for the merged child
        let rlp_node = only_child_node.as_rlp_node();

        let child_is_in_same_page = child_slotted_page.is_none();

        if child_is_in_same_page {
            // Child is on the same page
            self.merge_with_child_on_same_page(
                slotted_page,
                page_index,
                only_child_node,
                only_child_node_pointer,
                rlp_node,
            )
        } else {
            // Child is on another page
            self.merge_with_child_on_different_page(
                context,
                slotted_page,
                page_index,
                only_child_node,
                child_slotted_page.unwrap(),
                rlp_node,
            )
        }
    }

    /// Handles merging a branch with a child on the same page
    fn merge_with_child_on_same_page(
        &self,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        only_child_node: Node,
        only_child_node_pointer: &Pointer,
        rlp_node: RlpNode,
    ) -> Result<PointerChange, Error> {
        let child_cell_index =
            only_child_node_pointer.location().cell_index().expect("cell index should exist");

        // Delete both nodes and insert the merged one
        slotted_page.delete_value(child_cell_index)?;
        slotted_page.delete_value(page_index)?;

        let only_child_node_index = slotted_page.insert_value(&only_child_node)?;

        // If we are the root of the page, we must insert at index 0
        if page_index == 0 {
            assert_eq!(only_child_node_index, page_index);
        }

        Ok(PointerChange::Update(Pointer::new(
            node_location(slotted_page.id(), only_child_node_index),
            rlp_node,
        )))
    }

    // Handles merging a branch with a child on a different page
    fn merge_with_child_on_different_page(
        &mut self,
        context: &mut TransactionContext,
        slotted_page: &mut SlottedPageMut<'_>,
        page_index: u8,
        only_child_node: Node,
        mut child_slotted_page: SlottedPageMut<'_>,
        rlp_node: RlpNode,
    ) -> Result<PointerChange, Error> {
        let branch_page_id = slotted_page.id();

        // Ensure the child page has enough space
        if child_slotted_page.num_free_bytes() < 200 {
            self.split_page(context, &mut child_slotted_page)?;
            // Not returning Error::PageSplit because we're splitting the child page
        }

        // Delete ourselves and update the child
        slotted_page.delete_value(page_index)?;
        child_slotted_page.set_value(0, &only_child_node)?;

        // If we're the root node, orphan our page
        if page_index == 0 {
            self.meta_manager.orphan_pages().push(branch_page_id)?;
        }

        Ok(PointerChange::Update(Pointer::new(node_location(child_slotted_page.id(), 0), rlp_node)))
    }

    // Split the page into two, moving the largest immediate subtrie of the root node to a new child
    // page.
    fn split_page(
        &mut self,
        context: &mut TransactionContext,
        page: &mut SlottedPageMut<'_>,
    ) -> Result<(), Error> {
        while page.num_free_bytes() < Page::DATA_SIZE / 4_usize {
            let child_page = self.allocate_page(context)?;
            let mut child_slotted_page = SlottedPageMut::try_from(child_page)?;

            let mut root_node: Node = page.get_value(0)?;

            // Find the child with the largest subtrie
            let (largest_child_index, largest_child_pointer) = root_node
                .enumerate_children()?
                .into_iter()
                .max_by_key(|(_, ptr)| {
                    // If pointer points to a cell in current page, count nodes in that subtrie
                    if let Some(cell_index) = ptr.location().cell_index() {
                        count_subtrie_nodes(page, cell_index).unwrap_or(0)
                    } else {
                        // If pointer points to another page, count as 0
                        0
                    }
                })
                .ok_or(Error::PageError(PageError::PageIsFull))?;

            // Move the subtrie to the new page
            if let Some(cell_index) = largest_child_pointer.location().cell_index() {
                // Move all child nodes that are in the current page
                let location = move_subtrie_nodes(page, cell_index, &mut child_slotted_page)?;
                assert!(location.page_id().is_some(), "expected subtrie to be moved to a new page");

                // Update the pointer in the root node to point to the new page
                root_node.set_child(
                    largest_child_index,
                    Pointer::new(
                        Location::for_page(child_slotted_page.id()),
                        largest_child_pointer.rlp().clone(),
                    ),
                )?;
                page.set_value(0, &root_node)?;
            }
        }

        Ok(())
    }

    // Recursively deletes a subtrie from the page, orphaning any pages that become fully
    // unreferenced as a result.
    fn delete_subtrie(
        &mut self,
        context: &mut TransactionContext,
        slotted_page: &mut SlottedPageMut<'_>,
        cell_index: u8,
    ) -> Result<(), Error> {
        if cell_index == 0 {
            // if we are a root node, deleting ourself will orphan our entire page and
            // all of our descendant pages. Instead of deleting each cell one-by-one
            // we can orphan our entire page, and recursively orphan all our descendant
            // pages as well.
            return self.orphan_subtrie(context, slotted_page.id());
        }

        let node: Node = slotted_page.get_value(cell_index)?;

        if node.has_children() {
            let children = node.enumerate_children()?;

            for (_, child_ptr) in children {
                if let Some(cell_index) = child_ptr.location().cell_index() {
                    self.delete_subtrie(context, slotted_page, cell_index)?
                } else {
                    // the child is a root of another page, and that child will be
                    // deleted, essentially orphaning that page and all descendants of
                    // that page.
                    self.orphan_subtrie(
                        context,
                        child_ptr.location().page_id().expect("page_id must exist"),
                    )?
                }
            }
        }

        slotted_page.delete_value(cell_index)?;
        Ok(())
    }

    // Orphans a subtrie from the page, orphaning any pages that become fully unreferenced as a
    // result.
    fn orphan_subtrie(
        &mut self,
        context: &mut TransactionContext,
        page_id: PageId,
    ) -> Result<(), Error> {
        let page = self.get_page(context, page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;

        self.orphan_subtrie_helper(context, &slotted_page, 0)?;

        Ok(())
    }

    fn orphan_subtrie_helper(
        &mut self,
        context: &mut TransactionContext,
        slotted_page: &SlottedPage<'_>,
        cell_index: u8,
    ) -> Result<(), Error> {
        let node: Node = slotted_page.get_value(cell_index)?;

        if node.has_children() {
            let children = node.enumerate_children()?;

            for (_, child_ptr) in children {
                if let Some(cell_index) = child_ptr.location().cell_index() {
                    self.orphan_subtrie_helper(context, slotted_page, cell_index)?;
                } else {
                    // the child is a root of another page, and that child will be
                    // deleted, essentially orphaning that page and all descendants of
                    // that page.
                    let child_page = self.get_page(
                        context,
                        child_ptr.location().page_id().expect("page_id must exist"),
                    )?;
                    let child_slotted_page = SlottedPage::try_from(child_page)?;
                    self.orphan_subtrie_helper(context, &child_slotted_page, 0)?
                }
            }
        }

        if cell_index == 0 {
            self.meta_manager.orphan_pages().push(slotted_page.id())?;
        }

        Ok(())
    }

    /// Rolls back all outstanding data to disk. Currently unimplemented.
    pub fn rollback(&self, _context: &TransactionContext) -> Result<(), Error> {
        Ok(())
    }

    /// Returns the total number of pages in the storage engine.
    pub fn size(&self) -> u32 {
        self.page_manager.size()
    }

    fn get_slotted_page_and_index<'p>(
        &self,
        context: &TransactionContext,
        pointer: &Pointer,
        current_slotted_page: SlottedPage<'p>,
    ) -> Result<(SlottedPage<'p>, u8), Error> {
        if let Some(page_id) = pointer.location().page_id() {
            let page = self.get_page(context, page_id)?;
            let slotted_page = SlottedPage::try_from(page)?;
            Ok((slotted_page, 0))
        } else {
            let cell_index = pointer.location().cell_index().unwrap();
            Ok((current_slotted_page, cell_index))
        }
    }

    // Below functions are for debugging purposes- see 'cli/README.md' for more information'

    /// Writes the nodes and info of a given page of the trie to file, with children nested under
    /// parent branches. If page_id is None, writes the entire trie
    pub fn print_page<W: io::Write>(
        &self,
        context: &TransactionContext,
        mut buf: W,
        page_id: Option<PageId>,
    ) -> Result<(), Error> {
        let root_node_page_id = match context.root_node_page_id {
            None => return Ok(()),
            Some(page_id) => page_id,
        };

        let (page, print_whole_db) = match page_id {
            Some(id) => (self.get_page(context, id)?, false),
            None => (self.get_page(context, root_node_page_id)?, true),
        };

        let slotted_page = SlottedPage::try_from(page)?;
        self.print_page_helper(
            context,
            slotted_page,
            0,
            String::from(""),
            buf.by_ref(),
            print_whole_db,
        )
    }

    fn print_page_helper(
        &self,
        context: &TransactionContext,
        slotted_page: SlottedPage<'_>,
        cell_index: u8,
        indent: String,
        buf: &mut impl io::Write,
        print_whole_db: bool,
    ) -> Result<(), Error> {
        let node: Node = slotted_page.get_value(cell_index)?;

        match node {
            Node::AccountLeaf { ref storage_root, .. } => {
                StorageEngine::write_node_value(&node, slotted_page.id(), buf, &indent)?;
                let mut new_indent = indent.clone();
                new_indent.push('\t');

                if let Some(direct_child) = storage_root {
                    let (new_slotted_page, cell_index) =
                        self.get_slotted_page_and_index(context, direct_child, slotted_page)?;
                    // child is on different page, and we are only printing the current page
                    if new_slotted_page.id() != slotted_page.id() && !print_whole_db {
                        let child_page_id = direct_child.location().page_id().unwrap();
                        writeln!(buf, "{}Child on new page: {:?}", new_indent, child_page_id)?;
                        Ok(())
                    } else {
                        self.print_page_helper(
                            context,
                            new_slotted_page,
                            cell_index,
                            new_indent,
                            buf,
                            print_whole_db,
                        )
                    }
                } else {
                    writeln!(buf, "{}No direct child", new_indent)?;
                    Ok(())
                }
            }

            Node::Branch { prefix: _, ref children } => {
                StorageEngine::write_node_value(&node.clone(), slotted_page.id(), buf, &indent)?;
                for child in children.iter().flatten() {
                    let mut new_indent = indent.clone();
                    new_indent.push('\t');

                    //check if child is on same page
                    let (new_slotted_page, cell_index) =
                        self.get_slotted_page_and_index(context, child, slotted_page)?;
                    // child is on new page, and we are only printing the current page
                    if new_slotted_page.id() != slotted_page.id() && !print_whole_db {
                        let child_page_id = child.location().page_id().unwrap();
                        writeln!(buf, "{}Child on new page: {:?}", new_indent, child_page_id)?;
                        return Ok(())
                    } else {
                        self.print_page_helper(
                            context,
                            new_slotted_page,
                            cell_index,
                            new_indent,
                            buf,
                            print_whole_db,
                        )?
                    }
                }
                Ok(())
            }
            Node::StorageLeaf { prefix: _, value_rlp: _ } => {
                StorageEngine::write_node_value(&node, slotted_page.id(), buf, &indent)?;
                Ok(())
            }
        }
    }

    /// Prints information about a given TrieValue.
    /// Verbose option: writes information about nodes visited along the path to file
    /// Extra-verbose option: writes information about pages visited along path to file
    pub fn print_path<W: io::Write>(
        &self,
        context: &TransactionContext,
        path: &Nibbles,
        mut buf: W,
        verbosity_level: u8,
    ) -> Result<(), Error> {
        let page_id = match context.root_node_page_id {
            None => return Ok(()),
            Some(page_id) => page_id,
        };
        let page = self.get_page(context, page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;

        // If extra_verbose, print the root page first
        match verbosity_level {
            0 => (),
            1 => {
                //verbose; print page ID and nodes accessed from page
                writeln!(buf, "\nNODES ACCESSED FROM PAGE {}\n", page_id)?;
            }
            2 => {
                //extra verbose; print page ID, nodes accessed from page, and page contents
                writeln!(buf, "PAGE: {}\n", page_id)?;

                self.print_page(context, &mut buf, Some(page_id))?;
                writeln!(buf, "\nNODES ACCESSED FROM PAGE {}:", page_id)?;
            }
            _ => return Err(Error::DebugError("Invalid verbosity level".to_string())),
        }

        self.print_path_helper(context, path, 0, slotted_page, 0, buf.by_ref(), verbosity_level)
    }

    fn print_path_helper(
        &self,
        context: &TransactionContext,
        path: &Nibbles,
        path_offset: usize,
        slotted_page: SlottedPage<'_>,
        page_index: u8,
        buf: &mut impl io::Write,
        verbosity_level: u8,
    ) -> Result<(), Error> {
        let node: Node = slotted_page.get_value(page_index)?;

        if verbosity_level > 0 {
            // Write node information with indentation
            StorageEngine::write_node_value(&node, slotted_page.id(), buf, "")?;
        }

        let common_prefix_length =
            nybbles::common_prefix_length(&path[path_offset..], node.prefix());

        if common_prefix_length < node.prefix().len() {
            writeln!(buf, "NODE NOT FOUND\n")?;
            return Ok(());
        }

        let remaining_path = &path[path_offset + common_prefix_length..];

        if remaining_path.is_empty() {
            //write only this node's information to file
            writeln!(buf, "\n\nREQUESTED NODE:")?;
            StorageEngine::write_node_value(&node, slotted_page.id(), buf, "")?;

            return Ok(());
        }

        let (child_pointer, new_path_offset) = match node {
            AccountLeaf { ref storage_root, .. } => {
                (storage_root.as_ref(), path_offset + common_prefix_length)
            }
            Branch { ref children, .. } => (
                children[remaining_path[0] as usize].as_ref(),
                path_offset + common_prefix_length + 1,
            ),
            _ => unreachable!(),
        };

        match child_pointer {
            Some(child_pointer) => {
                let (child_slotted_page, child_cell_index) =
                    self.get_slotted_page_and_index(context, child_pointer, slotted_page)?;

                // If we're moving to a new page and extra_verbose is true, print the new page
                if child_slotted_page.id() != slotted_page.id() {
                    if verbosity_level == 2 {
                        //extra verbose; print new page contents
                        writeln!(buf, "\n\n\nNEW PAGE: {}\n", child_slotted_page.id())?;
                        self.print_page(context, &mut *buf, Some(child_slotted_page.id()))?;
                    }

                    if verbosity_level > 0 {
                        writeln!(buf, "\nNODES ACCESSED FROM PAGE {}\n", child_slotted_page.id())?;
                    }
                }

                self.print_path_helper(
                    context,
                    path,
                    new_path_offset,
                    child_slotted_page,
                    child_cell_index,
                    buf,
                    verbosity_level,
                )
            }

            None => {
                writeln!(buf, "NODE NOT FOUND\n")?;
                Ok(())
            }
        }
    }

    // Helper function to convert node information to string for printing/writing to file
    fn write_node_value<W: io::Write>(
        node: &Node,
        page_id: PageId,
        buf: &mut W,
        indent: &str,
    ) -> Result<(), Error> {
        match &node {
            Node::Branch { prefix, children } => {
                writeln!(
                    buf,
                    "{}Branch Node:  Page ID: {}  Children: {:?}, Prefix: {}",
                    indent,
                    page_id,
                    children
                        .iter()
                        .enumerate()
                        .filter(|(_, child)| child.is_some())
                        .map(|(i, _)| i.to_string())
                        .collect::<Vec<_>>(),
                    alloy_primitives::hex::encode(prefix.pack())
                )?;
                Ok(())
            }
            Node::AccountLeaf {
                prefix,
                nonce_rlp: _,
                balance_rlp: _,
                code_hash: _,
                storage_root: _,
            } => {
                match node.value() {
                    Ok(TrieValue::Account(acct)) => {
                        writeln!(
                            buf,
                            "{}AccountLeaf: nonce: {:?}, balance: {:?}, prefix: {}, code_hash: {:x?}, storage_root: {:?}",
                            indent,
                            acct.nonce, acct.balance, alloy_primitives::hex::encode(prefix.pack()), acct.code_hash, acct.storage_root,
                        )?;
                    }
                    _ => {
                        writeln!(buf, "{}AccountLeaf: no value ", indent)?;
                    }
                };
                Ok(())
            }
            Node::StorageLeaf { prefix, value_rlp: _ } => {
                match node.value() {
                    Ok(TrieValue::Storage(strg)) => {
                        let str_prefix = alloy_primitives::hex::encode(prefix.pack());
                        writeln!(
                            buf,
                            "{}StorageLeaf: storage: {:?}, prefix: {}",
                            indent, strg, str_prefix
                        )?;
                    }
                    _ => {
                        writeln!(buf, "{}StorageLeaf: no value", indent)?;
                    }
                };
                Ok(())
            }
        }
    }

    pub fn debug_statistics<W: io::Write>(
        &self,
        context: &TransactionContext,
        mut buf: W,
    ) -> Result<(), Error> {
        let page_id = match context.root_node_page_id {
            None => return Ok(()),
            Some(page_id) => page_id,
        };
        let page = self.get_page(context, page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;

        let mut stats = DebugPage::default();

        let occupied_bytes = slotted_page.num_occupied_bytes();
        let occupied_cells = slotted_page.num_occupied_cells();

        stats.bytes_per_page.update_stats(occupied_bytes);
        stats.nodes_per_page.update_stats(occupied_cells);

        self.debug_statistics_helper(context, slotted_page, 0, 1, 1, &mut stats)?;

        writeln!(buf, "Page Statistics: {:?}", stats)?;
        Ok(())
    }

    fn debug_statistics_helper(
        &self,
        context: &TransactionContext,
        slotted_page: SlottedPage<'_>,
        cell_index: u8,
        node_depth: usize,
        page_depth: usize,
        stats: &mut DebugPage,
    ) -> Result<(), Error> {
        let node: Node = slotted_page.get_value(cell_index)?;

        //update stats: total node size and prefix length
        stats.node_size_in_bytes.update_stats(node.size());
        stats.path_prefix_length.update_stats(node.prefix().len());

        match node {
            Node::AccountLeaf { storage_root, .. } => {
                //Note: direct child is not counted as part of stats.num_children
                if let Some(direct_child) = storage_root {
                    let (new_slotted_page, cell_index) =
                        self.get_slotted_page_and_index(context, &direct_child, slotted_page)?;
                    //if we move to a new page, update relevent stats
                    if new_slotted_page.id() != slotted_page.id() {
                        let occupied_bytes = new_slotted_page.num_occupied_bytes();
                        let occupied_cells = new_slotted_page.num_occupied_cells();

                        stats.bytes_per_page.update_stats(occupied_bytes);
                        stats.nodes_per_page.update_stats(occupied_cells);

                        self.debug_statistics_helper(
                            context,
                            new_slotted_page,
                            cell_index,
                            node_depth + 1,
                            page_depth + 1,
                            stats,
                        )
                    } else {
                        self.debug_statistics_helper(
                            context,
                            new_slotted_page,
                            cell_index,
                            node_depth + 1,
                            page_depth,
                            stats,
                        )
                    }
                } else {
                    stats.depth_of_trie_in_nodes.update_stats(node_depth);
                    stats.depth_of_trie_in_pages.update_stats(page_depth);
                    Ok(())
                }
            }

            Node::Branch { children, .. } => {
                //update num children per branch
                let child_iter = children.into_iter().flatten();
                let num_children = child_iter.clone().count();
                stats.num_children_per_branch.update_stats(num_children);

                for child in child_iter {
                    //check if child is on same page
                    let (new_slotted_page, cell_index) =
                        self.get_slotted_page_and_index(context, &child, slotted_page)?;
                    //update page depth if we move to a new page
                    if new_slotted_page.id() != slotted_page.id() {
                        let occupied_bytes = new_slotted_page.num_occupied_bytes();
                        let occupied_cells = new_slotted_page.num_occupied_cells();

                        stats.bytes_per_page.update_stats(occupied_bytes);
                        stats.nodes_per_page.update_stats(occupied_cells);
                        self.debug_statistics_helper(
                            context,
                            new_slotted_page,
                            cell_index,
                            node_depth + 1,
                            page_depth + 1,
                            stats,
                        )?
                    } else {
                        self.debug_statistics_helper(
                            context,
                            new_slotted_page,
                            cell_index,
                            node_depth + 1,
                            page_depth,
                            stats,
                        )?
                    }
                }
                Ok(())
            }
            Node::StorageLeaf { .. } => {
                stats.depth_of_trie_in_pages.update_stats(page_depth);
                stats.depth_of_trie_in_nodes.update_stats(node_depth);
                Ok(())
            }
        }
    }

    /// Traverses the trie from the given root node page id and returns a list of all reachable PageIds.
    pub fn consistency_check(
        &self,
        root_node_page_id: Option<PageId>,
        context: &TransactionContext,
    ) -> Result<HashSet<PageId>, Error> {
        let mut reachable = HashSet::new();

        // Start from the provided root node page id (if any)
        if let Some(root_page_id) = root_node_page_id {
            reachable.insert(root_page_id);
            self.consistency_check_helper(context, root_page_id, 0, &mut reachable)?;
        }
        // If there is a second root (e.g. for a second trie), traverse from there as well
        // (add logic here if needed for a second root)

        Ok(reachable)
    }

    fn consistency_check_helper(
        &self,
        context: &TransactionContext,
        page_id: PageId,
        cell_index: u8,
        reachable: &mut HashSet<PageId>,
    ) -> Result<(), Error> {
        let page = self.get_page(context, page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;
        let node: Node = slotted_page.get_value(cell_index)?;
        match node {
            Node::AccountLeaf { ref storage_root, .. } => {
                if let Some(direct_child) = storage_root {
                    let (new_slotted_page, new_cell_index) =
                        self.get_slotted_page_and_index(context, direct_child, slotted_page)?;
                    // If child is on a new page,insert the page into the set andrecurse
                    if new_slotted_page.id() != page_id {
                        reachable.insert(new_slotted_page.id());
                        self.consistency_check_helper(context, new_slotted_page.id(), new_cell_index, reachable)?;
                    } else {
                        self.consistency_check_helper(context, page_id, new_cell_index, reachable)?;
                    }
                }
            }
            Node::Branch { ref children, .. } => {
                for child in children.iter().flatten() {
                    let (new_slotted_page, new_cell_index) =
                        self.get_slotted_page_and_index(context, child, slotted_page.clone())?;
                    if new_slotted_page.id() != page_id {
                        self.consistency_check_helper(context, new_slotted_page.id(), new_cell_index, reachable)?;
                    } else {
                        self.consistency_check_helper(context, page_id, new_cell_index, reachable)?;
                    }
                }
            }
            Node::StorageLeaf { .. } => {}
        }
        Ok(())
    }
}

fn node_location(page_id: PageId, page_index: u8) -> Location {
    if page_index == 0 {
        Location::for_page(page_id)
    } else {
        Location::for_cell(page_index)
    }
}

/// Finds the index of the change with the shortest common prefix shared with the node
/// Returns the index of the change and the length of the common prefix
/// Requires that the changes list is sorted, otherwise the result is undefined.
fn find_shortest_common_prefix<T>(
    changes: &[(Nibbles, T)],
    path_offset: u8,
    node: &Node,
) -> (usize, usize) {
    let leftmost = changes.first().unwrap();
    let leftmost_path = &leftmost.0[path_offset as usize..];
    let rightmost = changes.last().unwrap();
    let rightmost_path = &rightmost.0[path_offset as usize..];

    debug_assert!(leftmost.0.cmp(&rightmost.0) <= Ordering::Equal, "changes must be sorted");
    debug_assert!(
        leftmost_path.cmp(rightmost_path) <= Ordering::Equal,
        "changes must be sorted after slicing with path offset"
    );

    let leftmost_prefix_length = nybbles::common_prefix_length(node.prefix(), leftmost_path);
    let rightmost_prefix_length = nybbles::common_prefix_length(node.prefix(), rightmost_path);

    if leftmost_prefix_length <= rightmost_prefix_length {
        (0, leftmost_prefix_length)
    } else {
        (changes.len() - 1, rightmost_prefix_length)
    }
}

// Helper function to count nodes in a subtrie on the given page
fn count_subtrie_nodes(page: &SlottedPage<'_>, root_index: u8) -> Result<u8, Error> {
    let mut count = 1; // Count the root node
    let node: Node = page.get_value(root_index)?;
    if !node.has_children() {
        return Ok(count);
    }

    // Count child nodes that are in this page
    for (_, child_ptr) in node.enumerate_children()? {
        if let Some(child_index) = child_ptr.location().cell_index() {
            count += count_subtrie_nodes(page, child_index)?;
        }
    }

    Ok(count)
}

// Helper function to move an entire subtrie from one page to another.
fn move_subtrie_nodes(
    source_page: &mut SlottedPageMut<'_>,
    root_index: u8,
    target_page: &mut SlottedPageMut<'_>,
) -> Result<Location, Error> {
    let node: Node = source_page.get_value(root_index)?;
    source_page.delete_value(root_index)?;

    let has_children = node.has_children();

    // first insert the node into the new page to secure its location.
    let new_index = target_page.insert_value(&node)?;

    // if the node has no children, we're done.
    if !has_children {
        return Ok(node_location(target_page.id(), new_index));
    }

    // otherwise, we need to move the children of the node.
    let mut updated_node: Node = target_page.get_value(new_index)?;

    // Process each child that's in the current page
    let range = if updated_node.is_branch() {
        0..16
    } else {
        // AccountLeaf's only have 1 child
        0..1
    };

    for branch_index in range {
        let child_ptr = if updated_node.is_account_leaf() {
            updated_node.direct_child()?
        } else {
            updated_node.child(branch_index)?
        };
        if let Some(child_ptr) = child_ptr {
            if let Some(child_index) = child_ptr.location().cell_index() {
                // Recursively move its children
                let new_location = move_subtrie_nodes(source_page, child_index, target_page)?;
                // update the pointer in the parent node
                updated_node
                    .set_child(branch_index, Pointer::new(new_location, child_ptr.rlp().clone()))?;
            }
        }
    }

    // update the parent node with the new child pointers.
    target_page.set_value(new_index, &updated_node)?;

    Ok(node_location(target_page.id(), new_index))
}

impl StorageEngine {
    /// Allocates a new page from the underlying page manager.
    /// If there is an orphaned page available as of the given [SnapshotId],
    /// it is used to allocate a new page instead.
    pub fn allocate_page<'p>(
        &mut self,
        context: &mut TransactionContext,
    ) -> Result<PageMut<'p>, Error> {
        let page_manager = &self.page_manager;
        let orphaned_page_id = self.meta_manager.orphan_pages().pop_if(|orphan_page_id| {
            let page = page_manager
                .get(context.snapshot_id, orphan_page_id)
                .expect("orphan page does not exist");
            page.snapshot_id() < self.alive_snapshot_id
        });

        let page_to_return = if let Some(orphaned_page_id) = orphaned_page_id {
            let mut page = self.get_mut_page(context, orphaned_page_id)?;
            page.set_snapshot_id(context.snapshot_id);
            page.contents_mut().fill(0);
            context.transaction_metrics.inc_pages_reallocated();
            page
        } else {
            let page = self.page_manager.allocate(context.snapshot_id)?;
            context.transaction_metrics.inc_pages_allocated();
            page
        };

        context.page_count = self.page_manager.size();

        Ok(page_to_return)
    }

    pub fn commit(&mut self, context: &TransactionContext) -> Result<(), Error> {
        self.page_manager.commit()?;

        let dirty_meta = self.meta_manager.dirty_slot_mut();
        context.update_metadata(dirty_meta);
        self.meta_manager.commit()?;

        Ok(())
    }

    /// Retrieves a mutable [Page] from the underlying [PageManager].
    pub fn get_mut_page<'p>(
        &mut self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<PageMut<'p>, Error> {
        let page = self.page_manager.get_mut(context.snapshot_id, page_id)?;
        context.transaction_metrics.inc_pages_read();
        Ok(page)
    }

    /// Retrieves a read-only [Page] from the underlying [PageManager].
    pub fn get_page<'p>(
        &self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<Page<'p>, Error> {
        let page = self.page_manager.get(context.snapshot_id, page_id)?;
        context.transaction_metrics.inc_pages_read();
        Ok(page)
    }
}

#[derive(Debug)]
pub enum Error {
    IO(io::Error),
    NodeError(NodeError),
    PageError(PageError),
    InvalidCommonPrefixIndex,
    InvalidSnapshotId,
    PageSplit(usize),
    DebugError(String),
}

impl From<PageError> for Error {
    fn from(error: PageError) -> Self {
        Self::PageError(error)
    }
}

impl From<NodeError> for Error {
    fn from(error: NodeError) -> Self {
        Self::NodeError(error)
    }
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Self::IO(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        account::Account,
        page::page_id,
        storage::{
            engine::PageError,
            test_utils::{
                assert_metrics, create_test_account, create_test_engine, random_test_account,
            },
        },
    };
    use alloy_primitives::{address, b256, hex, keccak256, Address, StorageKey, B256, U256};
    use alloy_trie::{
        root::{storage_root_unhashed, storage_root_unsorted},
        EMPTY_ROOT_HASH, KECCAK_EMPTY,
    };
    use proptest::prelude::*;
    use rand::{rngs::StdRng, seq::SliceRandom, Rng, RngCore, SeedableRng};
    use std::collections::HashMap;

    #[test]
    fn test_allocate_get_mut_clone() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        // Initial allocation
        let mut page = storage_engine.allocate_page(&mut context).unwrap();
        assert_eq!(page.id(), page_id!(1));
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 1);
        assert_metrics(&context, 0, 1, 0, 0);

        // mutation
        page.contents_mut()[0] = 123;
        storage_engine.commit(&context).unwrap();

        context = storage_engine.write_context();

        // reading mutated page
        let page = storage_engine.get_page(&context, page_id!(1)).unwrap();
        assert_eq!(page.id(), page_id!(1));
        assert_eq!(page.contents()[0], 123);
        assert_eq!(page.snapshot_id(), 1);
        assert_metrics(&context, 1, 0, 0, 0);

        // cloning a page should allocate a new page and orphan the original page
        let cloned_page = storage_engine.get_mut_clone(&mut context, page_id!(1)).unwrap();
        assert_eq!(cloned_page.id(), page_id!(2));
        assert_eq!(cloned_page.contents()[0], 123);
        assert_eq!(cloned_page.snapshot_id(), 2);
        assert_ne!(cloned_page.id(), page.id());
        assert_metrics(&context, 2, 1, 0, 0);

        // the next allocation should not come from the orphaned page, as the snapshot id is the
        // same as when the page was orphaned
        let page = storage_engine.allocate_page(&mut context).unwrap();
        assert_eq!(page.id(), 3);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 2);
        assert_metrics(&context, 2, 2, 0, 0);

        storage_engine.commit(&context).unwrap();

        context = storage_engine.write_context();

        // the next allocation should not come from the orphaned page, as the snapshot has not been
        // unlocked yet
        let page = storage_engine.allocate_page(&mut context).unwrap();
        assert_eq!(page.id(), 4);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 3);
        assert_metrics(&context, 0, 1, 0, 0);

        storage_engine.unlock(3);

        // the next allocation should come from the orphaned page because the snapshot id has
        // increased. The page data should be zeroed out.
        let page = storage_engine.allocate_page(&mut context).unwrap();
        assert_eq!(page.id(), 1);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 3);
        assert_metrics(&context, 1, 1, 1, 0);

        // assert that the metadata tracks the largest page number
        assert_eq!(context.page_count, 4);
    }

    #[test]
    fn test_shared_page_mutability() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let page1 = storage_engine.allocate_page(&mut context).unwrap();
        assert_eq!(page1.id(), page_id!(1));
        assert_eq!(page1.contents()[0], 0);
        assert_metrics(&context, 0, 1, 0, 0);

        let mut page2 = storage_engine.get_mut_page(&context, page_id!(1)).unwrap();
        page2.contents_mut()[0] = 123;
        assert_metrics(&context, 1, 1, 0, 0);

        storage_engine.commit(&context).unwrap();

        assert_eq!(page1.contents()[0], 123);
        assert_eq!(page2.contents()[0], 123);
        assert_metrics(&context, 1, 1, 0, 0);
    }

    #[test]
    fn test_set_get_account() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))]
                    .as_mut(),
            )
            .unwrap();
        assert_eq!(context.root_node_page_id, Some(page_id!(1)));
        assert_metrics(&context, 0, 1, 0, 0);

        let test_cases = vec![
            (address!("0x4200000000000000000000000000000000000015"), create_test_account(123, 456)),
            (address!("0x4200000000000000000000000000000000000016"), create_test_account(999, 999)),
            (
                address!("0x4200000000000000000000000000000000000002"),
                create_test_account(1000, 1000),
            ),
            (
                address!("0x4200000000000000000000000000000000000000"),
                create_test_account(1001, 1001),
            ),
        ];

        // Insert accounts and verify they don't exist before insertion
        for (address, account) in &test_cases {
            let path = AddressPath::for_address(*address);

            let read_account = storage_engine.get_account(&mut context, path.clone()).unwrap();
            assert_eq!(read_account, None);

            storage_engine
                .set_values(
                    &mut context,
                    vec![(path.into(), Some(account.clone().into()))].as_mut(),
                )
                .unwrap();
        }

        // Verify all accounts exist after insertion
        for (address, account) in test_cases {
            let read_account = storage_engine
                .get_account(&mut context, AddressPath::for_address(address))
                .unwrap();
            assert_eq!(read_account, Some(account));
        }
    }

    #[test]
    fn test_simple_trie_state_root_1() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let address1 = address!("0x8e64566b5eb8f595f7eb2b8d302f2e5613cb8bae");
        let account1 = create_test_account(1_000_000_000_000_000_000u64, 0);
        let path1 = AddressPath::for_address(address1);

        let address2 = address!("0xcea8f2236efa20c8fadeb9d66e398a6532cca6c8");
        let account2 = create_test_account(14_000_000_000_000_000_000u64, 1);
        let path2 = AddressPath::for_address(address2);

        storage_engine
            .set_values(
                &mut context,
                vec![
                    (path1.into(), Some(account1.clone().into())),
                    (path2.into(), Some(account2.clone().into())),
                ]
                .as_mut(),
            )
            .unwrap();
        assert_metrics(&context, 1, 1, 0, 0);

        assert_eq!(
            context.root_node_hash,
            b256!("0x0d9348243d7357c491e6a61f4b1305e77dc6acacdb8cc708e662f6a9bab6ca02")
        );
    }

    #[test]
    fn test_simple_trie_state_root_2() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let address1 = address!("0x000f3df6d732807ef1319fb7b8bb8522d0beac02");
        let account1 = Account::new(1, U256::from(0), EMPTY_ROOT_HASH, keccak256(hex!("0x3373fffffffffffffffffffffffffffffffffffffffe14604d57602036146024575f5ffd5b5f35801560495762001fff810690815414603c575f5ffd5b62001fff01545f5260205ff35b5f5ffd5b62001fff42064281555f359062001fff015500")));
        let path1 = AddressPath::for_address(address1);

        let address2 = address!("0x0000000000000000000000000000000000001000");
        let account2 = Account::new(1, U256::from(0x010000000000u64), EMPTY_ROOT_HASH, keccak256(hex!("0x366000602037602060003660206000720f3df6d732807ef1319fb7b8bb8522d0beac02620186a0f16000556000516001553d6002553d600060003e600051600355")));
        let path2 = AddressPath::for_address(address2);

        let address3 = address!("0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b");
        let account3 =
            Account::new(0, U256::from(0x3635c9adc5dea00000u128), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let path3 = AddressPath::for_address(address3);

        storage_engine
            .set_values(
                &mut context,
                vec![
                    (path1.into(), Some(account1.into())),
                    (path2.into(), Some(account2.into())),
                    (path3.into(), Some(account3.into())),
                ]
                .as_mut(),
            )
            .unwrap();
        assert_metrics(&context, 1, 1, 0, 0);

        assert_eq!(
            context.root_node_hash,
            b256!("0x6f78ee01791dd8a62b4e2e86fae3d7957df9fa7f7a717ae537f90bb0c79df296")
        );

        let account1_storage = [
            (B256::with_last_byte(0x0c), U256::from(0x0c)),
            (
                b256!("0x000000000000000000000000000000000000000000000000000000000000200b"),
                b256!("0x6c31fc15422ebad28aaf9089c306702f67540b53c7eea8b7d2941044b027100f").into(),
            ),
        ];

        let account2_storage = vec![
            (B256::with_last_byte(0x00), U256::from(0x01)),
            (
                B256::with_last_byte(0x01),
                b256!("0x6c31fc15422ebad28aaf9089c306702f67540b53c7eea8b7d2941044b027100f").into(),
            ),
            (B256::with_last_byte(0x02), U256::from(0x20)),
            (
                B256::with_last_byte(0x03),
                b256!("0x6c31fc15422ebad28aaf9089c306702f67540b53c7eea8b7d2941044b027100f").into(),
            ),
        ];

        let account3_updated =
            Account::new(1, U256::from(0x3635c9adc5de938d5cu128), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let mut changes = account1_storage
            .map(|(key, value)| {
                (
                    StoragePath::for_address_and_slot(address1, key).full_path(),
                    Some(TrieValue::Storage(value)),
                )
            })
            .to_vec();

        changes.extend(account2_storage.into_iter().map(|(key, value)| {
            (
                StoragePath::for_address_and_slot(address2, key).full_path(),
                Some(TrieValue::Storage(value)),
            )
        }));

        changes.push((
            AddressPath::for_address(address3).into(),
            Some(TrieValue::Account(account3_updated)),
        ));

        storage_engine.set_values(&mut context, changes.as_mut()).unwrap();
        assert_metrics(&context, 2, 1, 0, 0);

        assert_eq!(
            context.root_node_hash,
            b256!("0xf869dcb9ef8893f6b30bf495847fd99166aaf790ed962c468d11a826996ab2d2")
        );
    }

    #[test]
    fn test_trie_state_root_order_independence() {
        let mut rng = StdRng::seed_from_u64(1);

        // create 100 accounts with random addresses, balances, and storage values
        let mut accounts = Vec::new();
        for idx in 0..100 {
            let address = Address::random_with(&mut rng);
            let account = random_test_account(&mut rng);
            let mut storage = Vec::new();
            if idx % 10 == 0 {
                for _ in 0..rng.gen_range(1..25) {
                    let slot = StorageKey::random_with(&mut rng);
                    storage.push((slot, StorageValue::from(rng.next_u64())));
                }
            }
            accounts.push((address, account, storage));
        }

        let (mut storage_engine, mut context) = create_test_engine(30000);

        // insert accounts and storage in random order
        accounts.shuffle(&mut rng);
        let mut changes = vec![];
        for (address, account, mut storage) in accounts.clone() {
            changes.push((
                AddressPath::for_address(address).into(),
                Some(TrieValue::Account(account)),
            ));
            storage.shuffle(&mut rng);
            for (slot, value) in storage {
                changes.push((
                    StoragePath::for_address_and_slot(address, slot).full_path(),
                    Some(TrieValue::Storage(value)),
                ));
            }
        }
        storage_engine.set_values(&mut context, &mut changes).unwrap();

        // commit the changes
        storage_engine.commit(&context).unwrap();

        let state_root = context.root_node_hash;

        let mut expected_account_storage_roots = HashMap::new();

        // check that all of the values are correct
        for (address, account, storage) in accounts.clone() {
            let read_account = storage_engine
                .get_account(&mut context, AddressPath::for_address(address))
                .unwrap()
                .unwrap();
            assert_eq!(read_account.balance, account.balance);

            for (slot, value) in storage {
                let read_value = storage_engine
                    .get_storage(&mut context, StoragePath::for_address_and_slot(address, slot))
                    .unwrap();
                assert_eq!(read_value, Some(value));
            }

            expected_account_storage_roots.insert(address, read_account.storage_root);
        }

        let (mut storage_engine, mut context) = create_test_engine(30000);

        // insert accounts in a different random order, but only after inserting different values
        // first
        accounts.shuffle(&mut rng);
        for (address, _, mut storage) in accounts.clone() {
            storage_engine
                .set_values(
                    &mut context,
                    vec![(
                        AddressPath::for_address(address).into(),
                        Some(random_test_account(&mut rng).into()),
                    )]
                    .as_mut(),
                )
                .unwrap();

            storage.shuffle(&mut rng);
            for (slot, _) in storage {
                storage_engine
                    .set_values(
                        &mut context,
                        vec![(
                            StoragePath::for_address_and_slot(address, slot).into(),
                            Some(StorageValue::from(rng.next_u64()).into()),
                        )]
                        .as_mut(),
                    )
                    .unwrap();
            }
        }

        accounts.shuffle(&mut rng);
        for (address, account, mut storage) in accounts.clone() {
            storage_engine
                .set_values(
                    &mut context,
                    vec![(AddressPath::for_address(address).into(), Some(account.into()))].as_mut(),
                )
                .unwrap();

            storage.shuffle(&mut rng);
            for (slot, value) in storage {
                storage_engine
                    .set_values(
                        &mut context,
                        vec![(
                            StoragePath::for_address_and_slot(address, slot).into(),
                            Some(value.into()),
                        )]
                        .as_mut(),
                    )
                    .unwrap();
            }
        }

        // commit the changes
        storage_engine.commit(&context).unwrap();

        // check that all of the values are correct
        for (address, account, storage) in accounts.clone() {
            let read_account = storage_engine
                .get_account(&mut context, AddressPath::for_address(address))
                .unwrap()
                .unwrap();
            assert_eq!(read_account.balance, account.balance);
            assert_eq!(read_account.nonce, account.nonce);
            assert_eq!(read_account.storage_root, expected_account_storage_roots[&address]);
            for (slot, value) in storage {
                let read_value = storage_engine
                    .get_storage(&mut context, StoragePath::for_address_and_slot(address, slot))
                    .unwrap();
                assert_eq!(read_value, Some(value));
            }
        }

        // verify the state root is the same
        assert_eq!(state_root, context.root_node_hash);
    }

    #[test]
    fn test_set_get_account_common_prefix() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let test_accounts = vec![
            (hex!("00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"), create_test_account(100, 1)),
            (hex!("00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"), create_test_account(123, 456)),
            (hex!("00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003"), create_test_account(999, 999)),
            (hex!("00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000004"), create_test_account(1000, 1000)),
            (hex!("00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000030000000000000000000000000000000005"), create_test_account(1001, 1001)),
        ];

        // Insert all accounts
        for (nibbles, account) in test_accounts.iter() {
            let path = AddressPath::new(Nibbles::from_nibbles(*nibbles));
            storage_engine
                .set_values(
                    &mut context,
                    vec![(path.into(), Some(account.clone().into()))].as_mut(),
                )
                .unwrap();
        }

        // Verify all accounts exist
        for (nibbles, account) in test_accounts {
            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let read_account = storage_engine.get_account(&mut context, path).unwrap();
            assert_eq!(read_account, Some(account));
        }
    }

    #[test]
    fn test_split_page() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let test_accounts = vec![
            (hex!("00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"), create_test_account(100, 1)),
            (hex!("00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"), create_test_account(123, 456)),
            (hex!("00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003"), create_test_account(999, 999)),
            (hex!("00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000004"), create_test_account(1000, 1000)),
            (hex!("00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000030000000000000000000000000000000005"), create_test_account(1001, 1001)),
        ];

        // Insert accounts
        for (nibbles, account) in test_accounts.iter() {
            let path = AddressPath::new(Nibbles::from_nibbles(*nibbles));
            storage_engine
                .set_values(
                    &mut context,
                    vec![(path.into(), Some(account.clone().into()))].as_mut(),
                )
                .unwrap();
        }

        // Split the page
        let page = storage_engine.get_mut_page(&context, page_id!(1)).unwrap();
        let mut slotted_page = SlottedPageMut::try_from(page).unwrap();
        storage_engine.split_page(&mut context, &mut slotted_page).unwrap();

        // Verify all accounts still exist after split
        for (nibbles, account) in test_accounts {
            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let read_account = storage_engine.get_account(&mut context, path).unwrap();
            assert_eq!(read_account, Some(account));
        }
    }

    #[test]
    fn test_insert_get_1000_accounts() {
        let (mut storage_engine, mut context) = create_test_engine(5000);

        for i in 0..1000 {
            let path = address_path_for_idx(i);
            let account = create_test_account(i, i);
            storage_engine
                .set_values(
                    &mut context,
                    vec![(path.clone().into(), Some(account.clone().into()))].as_mut(),
                )
                .unwrap();
        }

        for i in 0..1000 {
            let path = address_path_for_idx(i);
            let account = storage_engine.get_account(&mut context, path.clone()).unwrap();
            assert_eq!(account, Some(create_test_account(i, i)));
        }
    }

    #[test]
    #[should_panic]
    fn test_set_storage_slot_with_no_account_panics() {
        let (mut storage_engine, mut context) = create_test_engine(300);
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");

        let storage_key =
            b256!("0x0000000000000000000000000000000000000000000000000000000000000000");
        let storage_value =
            b256!("0x0000000000000000000000000000000000000000000000000000000062617365");

        let storage_path = StoragePath::for_address_and_slot(address, storage_key);

        let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

        storage_engine
            .set_values(
                &mut context,
                vec![(storage_path.into(), Some(storage_value.into()))].as_mut(),
            )
            .unwrap();
    }

    #[test]
    fn test_get_account_storage_cache() {
        let (mut storage_engine, mut context) = create_test_engine(300);
        {
            // An account with no storage should not be cached
            let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96555");
            let address_path = AddressPath::for_address(address);
            let account = create_test_account(22, 22);

            storage_engine
                .set_values(
                    &mut context,
                    vec![(address_path.clone().into(), Some(account.clone().into()))].as_mut(),
                )
                .unwrap();

            let read_account =
                storage_engine.get_account(&mut context, address_path.clone()).unwrap().unwrap();
            assert_eq!(read_account, account);
            let cached_location = context.contract_account_loc_cache.get(address_path.to_nibbles());
            assert!(cached_location.is_none());
        }
        {
            // An account with storage should be cache when read the account first
            let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
            let address_path = AddressPath::for_address(address);
            let account = create_test_account(100, 1);

            storage_engine
                .set_values(
                    &mut context,
                    vec![(address_path.clone().into(), Some(account.clone().into()))].as_mut(),
                )
                .unwrap();

            let test_cases = vec![
                (
                    b256!("0x0000000000000000000000000000000000000000000000000000000000000000"),
                    b256!("0x0000000000000000000000000000000000000000000000000000000062617365"),
                ),
                (
                    b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
                    b256!("0x000000000000000000000000000000006274632040202439362c3434322e3735"),
                ),
                (
                    b256!("0x0000000000000000000000000000000000000000000000000000000000000002"),
                    b256!("0x0000000000000000000000000000000000000000000000000000747269656462"),
                ),
                (
                    b256!("0x0000000000000000000000000000000000000000000000000000000000000003"),
                    b256!("0x000000000000000000000000000000000000000000000000436f696e62617365"),
                ),
            ];
            storage_engine
                .set_values(
                    &mut context,
                    test_cases
                        .iter()
                        .map(|(key, value)| {
                            let storage_path = StoragePath::for_address_and_slot(address, *key);
                            let storage_value = StorageValue::from_be_slice(value.as_slice());
                            (storage_path.into(), Some(storage_value.into()))
                        })
                        .collect::<Vec<(Nibbles, Option<TrieValue>)>>()
                        .as_mut(),
                )
                .unwrap();

            let read_account = storage_engine
                .get_account(&mut context, AddressPath::for_address(address))
                .unwrap()
                .unwrap();
            assert_eq!(read_account.balance, account.balance);
            assert_eq!(read_account.nonce, account.nonce);
            assert_ne!(read_account.storage_root, EMPTY_ROOT_HASH);

            // the account should be cached
            let account_cache_location =
                context.contract_account_loc_cache.get(address_path.to_nibbles()).unwrap();
            assert_eq!(account_cache_location.0, 1);
            assert_eq!(account_cache_location.1, 2); // 0 is the branch page, 1 is the first EOA
                                                     // account, 2 is the this contract account

            // getting the storage slot should hit the cache
            let storage_path = StoragePath::for_address_and_slot(address, test_cases[0].0);
            let read_storage_slot =
                storage_engine.get_storage(&mut context, storage_path.clone()).unwrap();
            assert_eq!(
                read_storage_slot,
                Some(StorageValue::from_be_slice(
                    b256!("0x0000000000000000000000000000000000000000000000000000000062617365")
                        .as_slice()
                ))
            );
            assert_eq!(context.transaction_metrics.get_cache_storage_read(), (1, 0));
        }
        {
            // Write into the storage slot should invalidate the cache
            let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96066");
            let address_path = AddressPath::for_address(address);
            let account = create_test_account(234, 567);

            storage_engine
                .set_values(
                    &mut context,
                    vec![(address_path.clone().into(), Some(account.clone().into()))].as_mut(),
                )
                .unwrap();

            let test_cases = [
                (
                    b256!("0x0000000000000000000000000000000000000000000000000000000000000000"),
                    b256!("0x0000000000000000000000000000000000000000000000000000000062617365"),
                ),
                (
                    b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
                    b256!("0x000000000000000000000000000000006274632040202439362c3434322e3735"),
                ),
            ];
            storage_engine
                .set_values(
                    &mut context,
                    test_cases
                        .iter()
                        .map(|(key, value)| {
                            let storage_path = StoragePath::for_address_and_slot(address, *key);
                            let storage_value = StorageValue::from_be_slice(value.as_slice());
                            (storage_path.into(), Some(storage_value.into()))
                        })
                        .collect::<Vec<(Nibbles, Option<TrieValue>)>>()
                        .as_mut(),
                )
                .unwrap();

            storage_engine
                .get_account(&mut context, AddressPath::for_address(address))
                .unwrap()
                .unwrap();

            let test_cases = [
                (
                    b256!("0x0000000000000000000000000000000000000000000000000000000000000002"),
                    b256!("0x0000000000000000000000000000000000000000000000000000747269656462"),
                ),
                (
                    b256!("0x0000000000000000000000000000000000000000000000000000000000000003"),
                    b256!("0x000000000000000000000000000000000000000000000000436f696e62617365"),
                ),
            ];
            storage_engine
                .set_values(
                    &mut context,
                    test_cases
                        .iter()
                        .map(|(key, value)| {
                            let storage_path = StoragePath::for_address_and_slot(address, *key);
                            let storage_value = StorageValue::from_be_slice(value.as_slice());
                            (storage_path.into(), Some(storage_value.into()))
                        })
                        .collect::<Vec<(Nibbles, Option<TrieValue>)>>()
                        .as_mut(),
                )
                .unwrap();

            // the cache should be invalidated
            let account_cache_location =
                context.contract_account_loc_cache.get(address_path.to_nibbles());
            assert!(account_cache_location.is_none());
        }
    }

    #[test]
    fn test_set_get_account_storage_slots() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))]
                    .as_mut(),
            )
            .unwrap();
        assert_eq!(context.root_node_page_id, Some(page_id!(1)));

        let test_cases = vec![
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000000"),
                b256!("0x0000000000000000000000000000000000000000000000000000000062617365"),
            ),
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
                b256!("0x000000000000000000000000000000006274632040202439362c3434322e3735"),
            ),
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000002"),
                b256!("0x0000000000000000000000000000000000000000000000000000747269656462"),
            ),
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000003"),
                b256!("0x000000000000000000000000000000000000000000000000436f696e62617365"),
            ),
        ];

        // Insert storage slots and verify they don't exist before insertion
        for (storage_key, _) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);
            let read_storage_slot =
                storage_engine.get_storage(&mut context, storage_path.clone()).unwrap();
            assert_eq!(read_storage_slot, None);
        }
        storage_engine
            .set_values(
                &mut context,
                test_cases
                    .iter()
                    .map(|(key, value)| {
                        let storage_path = StoragePath::for_address_and_slot(address, *key);
                        let storage_value = StorageValue::from_be_slice(value.as_slice());
                        (storage_path.into(), Some(storage_value.into()))
                    })
                    .collect::<Vec<(Nibbles, Option<TrieValue>)>>()
                    .as_mut(),
            )
            .unwrap();

        // Verify all storage slots exist after insertion
        for (storage_key, storage_value) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);
            let read_storage_slot = storage_engine.get_storage(&mut context, storage_path).unwrap();
            let storage_value = StorageValue::from_be_slice(storage_value.as_slice());
            assert_eq!(read_storage_slot, Some(storage_value));
        }
    }

    #[test]
    fn test_set_get_account_storage_roots() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))]
                    .as_mut(),
            )
            .unwrap();
        assert_eq!(context.root_node_page_id, Some(page_id!(1)));

        let test_cases = vec![
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000000"),
                b256!("0x0000000000000000000000000000000000000000000000000000000062617365"),
            ),
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000002"),
                b256!("0x0000000000000000000000000000000000000000000000000000747269656462"),
            ),
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
                b256!("0x000000000000000000000000000000006274632040202439362c3434322e3735"),
            ),
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000003"),
                b256!("0x000000000000000000000000000000000000000000000000436f696e62617365"),
            ),
        ];

        // Insert storage slots and verify they don't exist before insertion
        for (storage_key, storage_value) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            let read_storage_slot =
                storage_engine.get_storage(&mut context, storage_path.clone()).unwrap();
            assert_eq!(read_storage_slot, None);

            let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

            storage_engine
                .set_values(
                    &mut context,
                    vec![(storage_path.into(), Some(storage_value.into()))].as_mut(),
                )
                .unwrap();
        }

        // Verify the storage roots is correct. The storage root should be equivalent to the hash
        // of a trie that was initially empty and then filled with these key/values.
        let expected_root = storage_root_unhashed(test_cases.into_iter().map(|(key, value)| {
            (key, U256::from_be_bytes::<32>(value.as_slice().try_into().unwrap()))
        }));

        let account = storage_engine
            .get_account(&mut context, AddressPath::for_address(address))
            .unwrap()
            .unwrap();

        assert_eq!(account.storage_root, expected_root);
    }

    #[test]
    fn test_set_get_many_accounts_storage_roots() {
        let (mut storage_engine, mut context) = create_test_engine(2000);

        for i in 0..100 {
            let address =
                Address::from_slice(&keccak256((i as u32).to_le_bytes()).as_slice()[0..20]);
            let path = AddressPath::for_address(address);
            let account = create_test_account(i, i);
            storage_engine
                .set_values(
                    &mut context,
                    vec![(path.into(), Some(account.clone().into()))].as_mut(),
                )
                .unwrap();
        }

        for i in 0..100 {
            let address =
                Address::from_slice(&keccak256((i as u32).to_le_bytes()).as_slice()[0..20]);
            let path = AddressPath::for_address(address);
            let mut keys_values = Vec::new();
            for j in 0..25 {
                let storage_slot_key: StorageKey = B256::repeat_byte(j as u8);
                let storage_slot_value: StorageValue = B256::with_last_byte(j as u8).into();

                let storage_path = StoragePath::for_address_and_slot(address, storage_slot_key);
                storage_engine
                    .set_values(
                        &mut context,
                        vec![(storage_path.clone().into(), Some(storage_slot_value.into()))]
                            .as_mut(),
                    )
                    .unwrap();

                keys_values.push((
                    B256::from_slice(storage_path.get_slot().pack().as_slice()),
                    storage_slot_value,
                ))
            }

            let expected_root = storage_root_unsorted(keys_values.into_iter());

            // check the storage root of the account
            let account = storage_engine.get_account(&mut context, path).unwrap().unwrap();

            assert_eq!(account.storage_root, expected_root);
        }
    }

    #[test]
    fn test_split_page_stress() {
        // Create a storage engine with limited pages to force splits
        let (mut storage_engine, mut context) = create_test_engine(5000);

        // Create a large number of accounts with different patterns to stress the trie

        // Pattern 1: Accounts with common prefixes to create deep branches
        let mut accounts = Vec::new();
        for i in 0..4096 {
            // Create paths with common prefixes but different endings
            let mut nibbles = [0u8; 64];
            // First 32 nibbles are the same
            for (j, nibble) in nibbles[0..32].iter_mut().enumerate() {
                *nibble = (j % 16) as u8;
            }
            // Last 30 nibbles vary
            for (j, nibble) in nibbles[32..64].iter_mut().enumerate() {
                *nibble = ((i + j) % 16) as u8;
            }

            nibbles[61] = (i % 16) as u8;
            nibbles[62] = ((i / 16) % 16) as u8;
            nibbles[63] = ((i / 256) % 16) as u8;

            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let account = create_test_account(i as u64 * 1000, i as u64);
            accounts.push((path, account));
        }

        // Pattern 2: Accounts with very different paths to create wide branches
        for i in 0..4096 {
            let mut nibbles = [0u8; 64];
            // Make each path start with a different nibble
            nibbles[0] = (i % 16) as u8;
            nibbles[1] = ((i / 16) % 16) as u8;
            nibbles[2] = ((i / 256) % 16) as u8;
            // Fill the rest with a pattern
            for (j, nibble) in nibbles[3..64].iter_mut().enumerate() {
                *nibble = ((i * j) % 16) as u8;
            }

            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let account = create_test_account(i as u64 * 2000, i as u64 * 2);
            accounts.push((path, account));
        }

        // Pattern 3: Accounts with paths that will cause specific branch splits
        for i in 0..4096 {
            let mut nibbles = [0u8; 64];
            // First half of paths share prefix, second half different
            if i < 50 {
                nibbles[0] = 10; // Arbitrary value
                for (j, nibble) in nibbles[1..62].iter_mut().enumerate() {
                    *nibble = ((i + j) % 16) as u8;
                }
            } else {
                nibbles[0] = 11; // Different arbitrary value
                for (j, nibble) in nibbles[1..62].iter_mut().enumerate() {
                    *nibble = ((i + j) % 16) as u8;
                }
            }

            nibbles[61] = (i % 16) as u8;
            nibbles[62] = ((i / 16) % 16) as u8;
            nibbles[63] = ((i / 256) % 16) as u8;

            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let account = create_test_account(i as u64 * 3000, i as u64 * 3);
            accounts.push((path, account));
        }

        // Ensure there are no duplicate paths
        let mut unique_paths = std::collections::HashSet::new();
        for (path, _) in &accounts {
            assert!(unique_paths.insert(path.clone()), "Duplicate path found: {:?}", path);
        }

        // Insert all accounts
        for (path, account) in &accounts {
            storage_engine
                .set_values(
                    &mut context,
                    vec![(path.clone().into(), Some(account.clone().into()))].as_mut(),
                )
                .unwrap();
        }

        // Verify all accounts exist with correct values
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine.get_account(&mut context, path.clone()).unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "Account mismatch for path: {:?}",
                path
            );
        }

        // Force multiple splits to stress the system
        // Find all pages in the trie and split them recursively
        let mut pages_to_split = vec![context.root_node_page_id.unwrap()];
        while let Some(page_id) = pages_to_split.pop() {
            let page_result = storage_engine.get_mut_page(&context, page_id);
            if matches!(page_result, Err(Error::PageError(PageError::PageNotFound(_)))) {
                break;
            }
            let mut slotted_page = SlottedPageMut::try_from(page_result.unwrap()).unwrap();

            // Try to split this page
            if storage_engine.split_page(&mut context, &mut slotted_page).is_ok() {
                // If split succeeded, add the new pages to be processed
                pages_to_split.push(page_id.inc().unwrap()); // New page created by split
            }
        }

        // Verify all accounts still exist with correct values after splits
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine.get_account(&mut context, path.clone()).unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "Account mismatch after split for path: {:?}",
                path
            );
        }

        // Add more accounts after splitting to ensure the structure is still valid
        let mut additional_accounts = Vec::new();
        for i in 0..50 {
            let mut nibbles = [0u8; 64];
            // Create some completely new paths
            nibbles[0] = 15; // Different from previous patterns
            for (j, nibble) in nibbles[1..62].iter_mut().enumerate() {
                *nibble = ((i * j + 7) % 16) as u8; // Different pattern
            }

            nibbles[62] = (i % 16) as u8;
            nibbles[63] = ((i / 16) % 16) as u8;

            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let account = create_test_account(i as u64 * 5000, i as u64 * 5);
            additional_accounts.push((path, account));
        }

        // Insert additional accounts
        storage_engine
            .set_values(
                &mut context,
                additional_accounts
                    .iter()
                    .map(|(path, account)| (path.clone().into(), Some(account.clone().into())))
                    .collect::<Vec<(Nibbles, Option<TrieValue>)>>()
                    .as_mut(),
            )
            .unwrap();

        // Verify all original accounts still exist
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine.get_account(&mut context, path.clone()).unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "Original account lost after adding new accounts"
            );
        }

        // Verify all new accounts exist
        for (path, expected_account) in &additional_accounts {
            let retrieved_account = storage_engine.get_account(&mut context, path.clone()).unwrap();
            assert_eq!(retrieved_account, Some(expected_account.clone()), "New account not found");
        }
        // Verify the pages split metric
        assert!(context.transaction_metrics.get_pages_split() > 0);
    }

    #[test]
    fn test_split_page_random_accounts() {
        use rand::{rngs::StdRng, Rng, SeedableRng};

        // Create a storage engine
        let (mut storage_engine, mut context) = create_test_engine(2000);

        // Use a seeded RNG for reproducibility
        let mut rng = StdRng::seed_from_u64(42);

        // Generate a large number of random accounts
        let mut accounts = Vec::new();
        for _ in 0..3000 {
            let mut nibbles = [0u8; 64];
            // Generate random nibbles
            for nibble in &mut nibbles {
                *nibble = rng.gen_range(0..16) as u8;
            }

            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let balance = rng.gen_range(0..1_000_000);
            let nonce = rng.gen_range(0..100);
            let account = create_test_account(balance, nonce);
            accounts.push((path, account));
        }

        // Insert all accounts
        storage_engine
            .set_values(
                &mut context,
                accounts
                    .clone()
                    .into_iter()
                    .map(|(path, account)| (path.into(), Some(account.into())))
                    .collect::<Vec<(Nibbles, Option<TrieValue>)>>()
                    .as_mut(),
            )
            .unwrap();

        // Verify all accounts exist with correct values
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine.get_account(&mut context, path.clone()).unwrap();
            assert_eq!(retrieved_account, Some(expected_account.clone()));
        }

        // Get all pages and force splits on them
        let mut page_ids = Vec::new();
        // Start with the root page
        page_ids.push(context.root_node_page_id.unwrap());

        // Process each page
        for i in 0..page_ids.len() {
            let page_id = page_ids[i];

            // Try to get and split the page
            if let Ok(page) = storage_engine.get_mut_page(&context, page_id) {
                if let Ok(mut slotted_page) = SlottedPageMut::try_from(page) {
                    // Force a split
                    let _ = storage_engine.split_page(&mut context, &mut slotted_page);

                    // Get the node to find child pages
                    if let Ok(node) = slotted_page.get_value::<Node>(0) {
                        // Add child pages to our list
                        for (_, child_ptr) in node.enumerate_children().expect("can get children") {
                            if let Some(child_page_id) = child_ptr.location().page_id() {
                                if !page_ids.contains(&child_page_id) {
                                    page_ids.push(child_page_id);
                                }
                            }
                        }
                    }
                }
            }
        }

        // Verify all accounts still exist with correct values after splits
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine.get_account(&mut context, path.clone()).unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "Account mismatch after splitting multiple pages"
            );
        }

        // Create a vector to store updates
        let mut updates = Vec::new();

        // Prepare updates for some existing accounts
        for (i, (path, _)) in accounts.iter().enumerate() {
            if i % 5 == 0 {
                // Update every 5th account
                let new_balance = rng.gen_range(0..1_000_000);
                let new_nonce = rng.gen_range(0..100);
                let new_account = create_test_account(new_balance, new_nonce);

                updates.push((i, path.clone(), new_account));
            }
        }

        // Apply the updates to both the trie and our test data
        for (idx, path, new_account) in &updates {
            // Update in the trie
            storage_engine
                .set_values(
                    &mut context,
                    vec![(path.clone().into(), Some(new_account.clone().into()))].as_mut(),
                )
                .unwrap();

            // Update in our test data
            accounts[*idx] = (path.clone(), new_account.clone());
        }

        // Verify all accounts have correct values after updates
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine.get_account(&mut context, path.clone()).unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "Account mismatch after updates"
            );
        }
    }

    #[test]
    fn test_delete_account() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))]
                    .as_mut(),
            )
            .unwrap();
        assert_metrics(&context, 0, 1, 0, 0);

        // Check that the account exists
        let read_account =
            storage_engine.get_account(&mut context, AddressPath::for_address(address)).unwrap();
        assert_eq!(read_account, Some(account.clone()));

        // Reset the context metrics
        context.transaction_metrics = Default::default();
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), None)].as_mut(),
            )
            .unwrap();
        assert_metrics(&context, 2, 0, 0, 0);

        // Verify the account is deleted
        let read_account =
            storage_engine.get_account(&mut context, AddressPath::for_address(address)).unwrap();
        assert_eq!(read_account, None);
    }

    #[test]
    fn test_delete_accounts() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))]
                    .as_mut(),
            )
            .unwrap();
        assert_eq!(context.root_node_page_id, Some(page_id!(1)));

        let test_cases = vec![
            (address!("0x4200000000000000000000000000000000000015"), create_test_account(123, 456)),
            (address!("0x4200000000000000000000000000000000000016"), create_test_account(999, 999)),
            (
                address!("0x4200000000000000000000000000000000000002"),
                create_test_account(1000, 1000),
            ),
            (
                address!("0x4200000000000000000000000000000000000000"),
                create_test_account(1001, 1001),
            ),
        ];

        // Insert accounts and verify they don't exist before insertion
        for (address, account) in &test_cases {
            let path = AddressPath::for_address(*address);

            let read_account = storage_engine.get_account(&mut context, path.clone()).unwrap();
            assert_eq!(read_account, None);

            storage_engine
                .set_values(
                    &mut context,
                    vec![(path.into(), Some(account.clone().into()))].as_mut(),
                )
                .unwrap();
        }

        // Verify all accounts exist after insertion
        for (address, account) in &test_cases {
            let read_account = storage_engine
                .get_account(&mut context, AddressPath::for_address(*address))
                .unwrap();
            assert_eq!(read_account, Some(account.clone()));
        }

        // Delete all accounts
        for (address, _) in &test_cases {
            storage_engine
                .set_values(
                    &mut context,
                    vec![(AddressPath::for_address(*address).into(), None)].as_mut(),
                )
                .unwrap();
        }

        // Verify that the accounts don't exist anymore
        for (address, _) in &test_cases {
            let read_account = storage_engine
                .get_account(&mut context, AddressPath::for_address(*address))
                .unwrap();
            assert_eq!(read_account, None);
        }
    }

    #[test]
    fn test_some_delete_accounts() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))]
                    .as_mut(),
            )
            .unwrap();
        assert_eq!(context.root_node_page_id, Some(page_id!(1)));

        let test_cases = vec![
            (address!("0x4200000000000000000000000000000000000015"), create_test_account(123, 456)),
            (address!("0x4200000000000000000000000000000000000016"), create_test_account(999, 999)),
            (
                address!("0x4200000000000000000000000000000000000002"),
                create_test_account(1000, 1000),
            ),
            (
                address!("0x4200000000000000000000000000000000000000"),
                create_test_account(1001, 1001),
            ),
        ];

        // Insert accounts and verify they don't exist before insertion
        for (address, account) in &test_cases {
            let path = AddressPath::for_address(*address);

            let read_account = storage_engine.get_account(&mut context, path.clone()).unwrap();
            assert_eq!(read_account, None);

            storage_engine
                .set_values(
                    &mut context,
                    vec![(path.into(), Some(account.clone().into()))].as_mut(),
                )
                .unwrap();
        }

        // Verify all accounts exist after insertion
        for (address, account) in &test_cases {
            let read_account = storage_engine
                .get_account(&mut context, AddressPath::for_address(*address))
                .unwrap();
            assert_eq!(read_account, Some(account.clone()));
        }

        // Delete only a portion of the accounts
        for (address, _) in &test_cases[0..2] {
            storage_engine
                .set_values(
                    &mut context,
                    vec![(AddressPath::for_address(*address).into(), None)].as_mut(),
                )
                .unwrap();
        }

        // Verify that the accounts don't exist anymore
        for (address, _) in &test_cases[0..2] {
            let read_account = storage_engine
                .get_account(&mut context, AddressPath::for_address(*address))
                .unwrap();
            assert_eq!(read_account, None);
        }

        // Verify that the non-deleted accounts still exist
        for (address, account) in &test_cases[2..] {
            let read_account = storage_engine
                .get_account(&mut context, AddressPath::for_address(*address))
                .unwrap();
            assert_eq!(read_account, Some(account.clone()));
        }
    }

    #[test]
    fn test_delete_storage() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))]
                    .as_mut(),
            )
            .unwrap();
        assert_eq!(context.root_node_page_id, Some(page_id!(1)));

        let test_cases = vec![
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000000"),
                b256!("0x0000000000000000000000000000000000000000000000000000000062617365"),
            ),
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000002"),
                b256!("0x0000000000000000000000000000000000000000000000000000747269656462"),
            ),
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
                b256!("0x000000000000000000000000000000006274632040202439362c3434322e3735"),
            ),
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000003"),
                b256!("0x000000000000000000000000000000000000000000000000436f696e62617365"),
            ),
        ];

        // Insert storage slots and verify they don't exist before insertion
        for (storage_key, storage_value) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            let read_storage_slot =
                storage_engine.get_storage(&mut context, storage_path.clone()).unwrap();
            assert_eq!(read_storage_slot, None);

            let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

            storage_engine
                .set_values(
                    &mut context,
                    vec![(storage_path.into(), Some(storage_value.into()))].as_mut(),
                )
                .unwrap();
        }

        // Verify that we get all the storage values
        for (storage_key, storage_value) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

            let read_storage_slot =
                storage_engine.get_storage(&mut context, storage_path.clone()).unwrap();
            assert_eq!(read_storage_slot, Some(storage_value));
        }

        // Verify our storage root with alloy
        let mut keys_values: Vec<(B256, U256)> = test_cases
            .clone()
            .into_iter()
            .map(|(key, value)| {
                (key, U256::from_be_bytes::<32>(value.as_slice().try_into().unwrap()))
            })
            .collect();
        let expected_root = storage_root_unhashed(keys_values.clone());
        let account = storage_engine
            .get_account(&mut context, AddressPath::for_address(address))
            .unwrap()
            .unwrap();

        assert_eq!(account.storage_root, expected_root);

        // Delete storage one at a time
        for (storage_key, _) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            storage_engine
                .set_values(&mut context, vec![(storage_path.clone().into(), None)].as_mut())
                .unwrap();

            let read_storage_slot =
                storage_engine.get_storage(&mut context, storage_path.clone()).unwrap();

            assert_eq!(read_storage_slot, None);

            // check that the storage root is consistent
            keys_values.remove(0);
            let expected_root = storage_root_unhashed(keys_values.clone());
            let account = storage_engine
                .get_account(&mut context, AddressPath::for_address(address))
                .unwrap()
                .unwrap();

            assert_eq!(account.storage_root, expected_root);
        }
    }

    #[test]
    fn test_delete_account_also_deletes_storage() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))]
                    .as_mut(),
            )
            .unwrap();
        assert_eq!(context.root_node_page_id, Some(page_id!(1)));

        let test_cases = vec![
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000000"),
                b256!("0x0000000000000000000000000000000000000000000000000000000062617365"),
            ),
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000002"),
                b256!("0x0000000000000000000000000000000000000000000000000000747269656462"),
            ),
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
                b256!("0x000000000000000000000000000000006274632040202439362c3434322e3735"),
            ),
            (
                // storage key and storage value
                b256!("0x0000000000000000000000000000000000000000000000000000000000000003"),
                b256!("0x000000000000000000000000000000000000000000000000436f696e62617365"),
            ),
        ];

        // Insert storage slots and verify they don't exist before insertion
        for (storage_key, storage_value) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            let read_storage_slot =
                storage_engine.get_storage(&mut context, storage_path.clone()).unwrap();
            assert_eq!(read_storage_slot, None);

            let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

            storage_engine
                .set_values(
                    &mut context,
                    vec![(storage_path.into(), Some(storage_value.into()))].as_mut(),
                )
                .unwrap();
        }

        // Verify that we get all the storage values
        for (storage_key, storage_value) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

            let read_storage_slot =
                storage_engine.get_storage(&mut context, storage_path.clone()).unwrap();
            assert_eq!(read_storage_slot, Some(storage_value));
        }

        // Delete the account
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), None)].as_mut(),
            )
            .unwrap();

        // Verify the account no longer exists
        let res =
            storage_engine.get_account(&mut context, AddressPath::for_address(address)).unwrap();
        assert_eq!(res, None);

        // Verify all the storage slots don't exist
        for (storage_key, _) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            let res = storage_engine.get_storage(&mut context, storage_path.clone()).unwrap();
            assert_eq!(res, None);
        }

        // Now create a new account with the same address again and set storage
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))]
                    .as_mut(),
            )
            .unwrap();

        // Verify all the storage slots still don't exist
        for (storage_key, _) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            let read_storage =
                storage_engine.get_storage(&mut context, storage_path.clone()).unwrap();
            assert_eq!(read_storage, None);
        }
    }

    #[test]
    fn test_delete_single_child_branch_on_same_page() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        // GIVEN: a branch node with 2 children, where all the children live on the same page
        let mut account_1_nibbles = [0u8; 64];
        account_1_nibbles[0] = 1;

        let mut account_2_nibbles = [0u8; 64];
        account_2_nibbles[0] = 11;

        let account1 = create_test_account(100, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(
                    AddressPath::new(Nibbles::from_nibbles(account_1_nibbles)).into(),
                    Some(account1.clone().into()),
                )]
                .as_mut(),
            )
            .unwrap();

        let account2 = create_test_account(101, 2);
        storage_engine
            .set_values(
                &mut context,
                vec![(
                    AddressPath::new(Nibbles::from_nibbles(account_2_nibbles)).into(),
                    Some(account2.clone().into()),
                )]
                .as_mut(),
            )
            .unwrap();
        assert_eq!(context.root_node_page_id, Some(page_id!(1)));

        let page = storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
        let slotted_page = SlottedPage::try_from(page).unwrap();
        let node: Node = slotted_page.get_value(0).unwrap();
        assert!(node.is_branch());

        // WHEN: one of these accounts is deleted
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::new(Nibbles::from_nibbles(account_1_nibbles)).into(), None)]
                    .as_mut(),
            )
            .unwrap();

        // THEN: the root node should be a leaf node containing the remaining account
        //
        // first verify the deleted account is gone and the remaining account exists
        let read_account1 = storage_engine
            .get_account(&mut context, AddressPath::new(Nibbles::from_nibbles(account_1_nibbles)))
            .unwrap();
        assert_eq!(read_account1, None);

        let read_account2 = storage_engine
            .get_account(&mut context, AddressPath::new(Nibbles::from_nibbles(account_2_nibbles)))
            .unwrap();
        assert_eq!(read_account2, Some(account2));

        // check the the root node is a leaf
        let page = storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
        let slotted_page = SlottedPage::try_from(page).unwrap();
        let node: Node = slotted_page.get_value(0).unwrap();
        assert!(!node.is_branch());
    }

    #[test]
    fn test_delete_single_child_non_root_branch_on_different_pages() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        // GIVEN: a non-root branch node with 2 children where both children are on a different
        // pages
        //
        // first we construct a root branch node.
        let mut account_1_nibbles = [0u8; 64];
        account_1_nibbles[0] = 1;

        let mut account_2_nibbles = [0u8; 64];
        account_2_nibbles[0] = 11;

        let account1 = create_test_account(100, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(
                    AddressPath::new(Nibbles::from_nibbles(account_1_nibbles)).into(),
                    Some(account1.clone().into()),
                )]
                .as_mut(),
            )
            .unwrap();

        let account2 = create_test_account(101, 2);
        storage_engine
            .set_values(
                &mut context,
                vec![(
                    AddressPath::new(Nibbles::from_nibbles(account_2_nibbles)).into(),
                    Some(account2.clone().into()),
                )]
                .as_mut(),
            )
            .unwrap();
        assert_eq!(context.root_node_page_id, Some(page_id!(1)));

        let page = storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
        let slotted_page = SlottedPage::try_from(page).unwrap();
        let mut root_node: Node = slotted_page.get_value(0).unwrap();
        assert!(root_node.is_branch());

        let test_account = create_test_account(424, 234);

        // next we will force add a branch node in the middle of the root node (index 5)

        // page1 will hold our root node and the branch node
        let page1 =
            storage_engine.get_mut_page(&context, context.root_node_page_id.unwrap()).unwrap();
        let mut slotted_page1 = SlottedPageMut::try_from(page1).unwrap();

        // page2 will hold our 1st child
        let page2 = storage_engine.allocate_page(&mut context).unwrap();
        let mut slotted_page2 = SlottedPageMut::try_from(page2).unwrap();

        // page3 will hold our 2nd child
        let page3 = storage_engine.allocate_page(&mut context).unwrap();
        let mut slotted_page3 = SlottedPageMut::try_from(page3).unwrap();

        // we will force add 2 children to this branch node
        let mut child_1_full_path = [0u8; 64];
        child_1_full_path[0] = 5; // root branch nibble
        child_1_full_path[1] = 0; // inner branch nibble
        child_1_full_path[2] = 10; // leaf prefix
        child_1_full_path[3] = 11; // leaf prefix
        child_1_full_path[4] = 12; // leaf prefix
        let child_1: Node = Node::new_leaf(
            Nibbles::from_nibbles(&child_1_full_path[2..]),
            &TrieValue::Account(test_account.clone()),
        )
        .expect("can create node");

        let mut child_2_full_path = [0u8; 64];
        child_2_full_path[0] = 5; // root branch nibble
        child_2_full_path[1] = 15; // inner branch nibble
        child_2_full_path[2] = 1; // leaf prefix
        child_2_full_path[3] = 2; // leaf prefix
        child_2_full_path[4] = 3; // leaf prefix
        let child_2: Node = Node::new_leaf(
            Nibbles::from_nibbles(&child_2_full_path[2..]),
            &TrieValue::Account(test_account.clone()),
        )
        .expect("can create node");

        // child 1 is the root of page2
        slotted_page2.insert_value(&child_1).unwrap();
        let child_1_location = Location::from(slotted_page2.id());

        // child 2 is the root of page3
        slotted_page3.insert_value(&child_2).unwrap();
        let child_2_location = Location::from(slotted_page3.id());

        let mut new_branch_node: Node = Node::new_branch(Nibbles::new()).expect("can create node");
        new_branch_node
            .set_child(0, Pointer::new(child_1_location, RlpNode::default()))
            .expect("can set child");
        new_branch_node
            .set_child(15, Pointer::new(child_2_location, RlpNode::default()))
            .expect("can set child");
        let new_branch_node_index = slotted_page1.insert_value(&new_branch_node).unwrap();
        let new_branch_node_location = Location::from(new_branch_node_index as u32);

        root_node
            .set_child(5, Pointer::new(new_branch_node_location, RlpNode::default()))
            .expect("can set child");
        slotted_page1.set_value(0, &root_node).unwrap();

        storage_engine.commit(&context).unwrap();

        // assert we can get the child account we just added:
        let child_1_nibbles = Nibbles::from_nibbles(child_1_full_path);
        let child_2_nibbles = Nibbles::from_nibbles(child_2_full_path);
        let read_account1 = storage_engine
            .get_account(&mut context, AddressPath::new(child_1_nibbles.clone()))
            .unwrap();
        assert_eq!(read_account1, Some(test_account.clone()));
        let read_account2 = storage_engine
            .get_account(&mut context, AddressPath::new(child_2_nibbles.clone()))
            .unwrap();
        assert_eq!(read_account2, Some(test_account.clone()));

        // WHEN: child 1 is deleted
        let child_1_path = Nibbles::from_nibbles(child_1_full_path);
        storage_engine
            .set_values(&mut context, vec![(AddressPath::new(child_1_path).into(), None)].as_mut())
            .unwrap();

        // THEN: the branch node should be deleted and the root node should go to child 2 leaf at
        // index 5
        let root_node: Node = slotted_page.get_value(0).unwrap();
        assert!(root_node.is_branch());
        let child_2_pointer = root_node.child(5).expect("can get child").unwrap();
        assert!(child_2_pointer.location().page_id().is_some());
        assert_eq!(child_2_pointer.location().page_id().unwrap(), slotted_page3.id());

        // check that the prefix for child 2 has changed
        let child_2_node: Node = slotted_page3.get_value(0).unwrap();
        assert!(!child_2_node.is_branch());
        assert_eq!(child_2_node.prefix().clone(), Nibbles::from_nibbles(&child_2_full_path[1..]));

        // test that we can get child 2 and not child 1
        let read_account2 =
            storage_engine.get_account(&mut context, AddressPath::new(child_2_nibbles)).unwrap();
        assert_eq!(read_account2, Some(test_account.clone()));
        let read_account1 =
            storage_engine.get_account(&mut context, AddressPath::new(child_1_nibbles)).unwrap();
        assert_eq!(read_account1, None);
    }

    #[test]
    fn test_delete_single_child_root_branch_on_different_pages() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        // GIVEN: a root branch node with 2 children where both children are on a different page
        //
        // first we construct our two children on separate pages.
        let test_account = create_test_account(424, 234);

        // page2 will hold our 1st child
        let page2 = storage_engine.allocate_page(&mut context).unwrap();
        let mut slotted_page2 = SlottedPageMut::try_from(page2).unwrap();

        // page3 will hold our 2nd child
        let page3 = storage_engine.allocate_page(&mut context).unwrap();
        let mut slotted_page3 = SlottedPageMut::try_from(page3).unwrap();

        // we will force add 2 children to our root node
        let mut child_1_full_path = [0u8; 64];
        child_1_full_path[0] = 0; // root branch nibble
        child_1_full_path[2] = 10; // leaf prefix
        child_1_full_path[3] = 11; // leaf prefix
        child_1_full_path[4] = 12; // leaf prefix
        let child_1: Node = Node::new_leaf(
            Nibbles::from_nibbles(&child_1_full_path[1..]),
            &TrieValue::Account(test_account.clone()),
        )
        .expect("can create node");

        let mut child_2_full_path = [0u8; 64];
        child_2_full_path[0] = 15; // root branch nibble
        child_2_full_path[2] = 1; // leaf prefix
        child_2_full_path[3] = 2; // leaf prefix
        child_2_full_path[4] = 3; // leaf prefix
        let child_2: Node = Node::new_leaf(
            Nibbles::from_nibbles(&child_2_full_path[1..]),
            &TrieValue::Account(test_account.clone()),
        )
        .expect("can create node");

        // child 1 is the root of page2
        slotted_page2.insert_value(&child_1).unwrap();
        let child_1_location = Location::from(slotted_page2.id());

        // child 2 is the root of page3
        slotted_page3.insert_value(&child_2).unwrap();
        let child_2_location = Location::from(slotted_page3.id());

        // next we create and update our root node
        let mut root_node = Node::new_branch(Nibbles::new()).expect("can create node");
        root_node
            .set_child(0, Pointer::new(child_1_location, RlpNode::default()))
            .expect("can set child");
        root_node
            .set_child(15, Pointer::new(child_2_location, RlpNode::default()))
            .expect("can set child");

        let root_node_page = storage_engine.allocate_page(&mut context).unwrap();
        context.root_node_page_id = Some(root_node_page.id());
        let mut slotted_page = SlottedPageMut::try_from(root_node_page).unwrap();
        let root_index = slotted_page.insert_value(&root_node).unwrap();
        assert_eq!(root_index, 0);

        // not necessary but let's commit our changes.
        storage_engine.commit(&context).unwrap();

        // assert we can get the children accounts we just added:
        let child_1_nibbles = Nibbles::from_nibbles(child_1_full_path);
        let child_2_nibbles = Nibbles::from_nibbles(child_2_full_path);
        let read_account1 = storage_engine
            .get_account(&mut context, AddressPath::new(child_1_nibbles.clone()))
            .unwrap();
        assert_eq!(read_account1, Some(test_account.clone()));
        let read_account2 = storage_engine
            .get_account(&mut context, AddressPath::new(child_2_nibbles.clone()))
            .unwrap();
        assert_eq!(read_account2, Some(test_account.clone()));

        // WHEN: child 1 is deleted
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::new(child_1_nibbles.clone()).into(), None)].as_mut(),
            )
            .unwrap();

        // THEN: the root branch node should be deleted and the root node should be the leaf of
        // child 2 on the child's page
        let root_node_page =
            storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
        let root_node_slotted = SlottedPage::try_from(root_node_page).unwrap();
        let root_node: Node = root_node_slotted.get_value(0).unwrap();
        assert!(!root_node.is_branch());
        assert_eq!(root_node_slotted.id(), child_2_location.page_id().unwrap());

        // check that the prefix for root node has changed
        assert_eq!(root_node.prefix().clone(), child_2_nibbles);

        // test that we can get child 2 and not child 1
        let read_account2 =
            storage_engine.get_account(&mut context, AddressPath::new(child_2_nibbles)).unwrap();
        assert_eq!(read_account2, Some(test_account.clone()));
        let read_account1 =
            storage_engine.get_account(&mut context, AddressPath::new(child_1_nibbles)).unwrap();
        assert_eq!(read_account1, None);
    }

    #[test]
    fn test_delete_non_existent_value_doesnt_change_trie_structure() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        // GIVEN: a trie with a single account
        let address_nibbles = Nibbles::unpack(hex!(
            "0xf80f21938e5248ec70b870ac1103d0dd01b7811550a7a5c971e1c3e85ea62492"
        ));
        let account = create_test_account(100, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::new(address_nibbles).into(), Some(account.clone().into()))]
                    .as_mut(),
            )
            .unwrap();
        assert_eq!(context.root_node_page_id, Some(page_id!(1)));
        let root_subtrie_page =
            storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
        let root_subtrie_contents_before = root_subtrie_page.contents().to_vec();

        // WHEN: an account with a similiar but divergent path is deleted
        let address_nibbles = Nibbles::unpack(hex!(
            "0xf80f21938e5248ec70b870ac1103d0dd01b7811550a7ffffffffffffffffffff"
        ));
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::new(address_nibbles).into(), None)].as_mut(),
            )
            .unwrap();

        // THEN: the trie should remain unchanged
        let root_subtrie_page =
            storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
        let root_subtrie_contents_after = root_subtrie_page.contents().to_vec();
        assert_eq!(root_subtrie_contents_before, root_subtrie_contents_after);

        //**Additional Test**//

        // GIVEN: a trie with a branch node
        let address = address!("0xe8da6bf26964af9d7eed9e03e53415d37aa96045"); // first nibble is different, hash should force a branch node
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))]
                    .as_mut(),
            )
            .unwrap();
        let root_node_page =
            storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
        let root_subtrie_contents_before = root_node_page.contents().to_vec();
        let root_node_slotted_page = SlottedPage::try_from(root_node_page).unwrap();
        let root_node: Node = root_node_slotted_page.get_value(0).unwrap();
        assert!(root_node.is_branch());

        // WHEN: a non-existent value is deleted from the branch node
        let address = address!("0xf8da6bf26964af9d7eed9e03e53415d37aa96045"); // first nibble is different, hash doesn't exist
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), None)].as_mut(),
            )
            .unwrap();

        // THEN: the trie should remain unchanged
        let root_subtrie_page =
            storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
        let root_subtrie_contents_after = root_subtrie_page.contents().to_vec();
        assert_eq!(root_subtrie_contents_before, root_subtrie_contents_after);
    }

    #[test]
    fn test_leaf_update_and_non_existent_delete_works() {
        let (mut storage_engine, mut context) = create_test_engine(300);

        // GIVEN: a trie with a single account
        let address_nibbles_original_account = Nibbles::unpack(hex!(
            "0xf80f21938e5248ec70b870ac1103d0dd01b7811550a7a5c971e1c3e85ea62492"
        ));
        let account = create_test_account(100, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(
                    AddressPath::new(address_nibbles_original_account.clone()).into(),
                    Some(account.clone().into()),
                )]
                .as_mut(),
            )
            .unwrap();

        // WHEN: the same account is modified alongside a delete operation of a non existent value
        let address_nibbles = Nibbles::unpack(hex!(
            "0xf80f21938e5248ec70b870ac1103d0dd01b7811550a7ffffffffffffffffffff"
        ));

        let updated_account = create_test_account(300, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![
                    (
                        AddressPath::new(address_nibbles_original_account.clone()).into(),
                        Some(updated_account.clone().into()),
                    ),
                    (AddressPath::new(address_nibbles).into(), None),
                ]
                .as_mut(),
            )
            .unwrap();

        // THEN: the updated account should be updated
        let account_in_database = storage_engine
            .get_account(&mut context, AddressPath::new(address_nibbles_original_account))
            .unwrap()
            .unwrap();
        assert_eq!(account_in_database, updated_account);
    }

    fn address_path_for_idx(idx: u64) -> AddressPath {
        let mut nibbles = [0u8; 64];
        let mut val = idx;
        let mut pos = 63;
        while val > 0 {
            nibbles[pos] = (val % 16) as u8;
            val /= 16;
            pos -= 1;
        }
        AddressPath::new(Nibbles::from_nibbles(nibbles))
    }

    proptest! {
        #[test]
        fn fuzz_insert_get_accounts(
            accounts in prop::collection::vec(
                (any::<Address>(), any::<Account>()),
                1..100
            )
        ) {
            let (mut storage_engine, mut context) = create_test_engine(10_000);

            for (address, account) in &accounts {
                storage_engine
                    .set_values(&mut context, vec![(AddressPath::for_address(*address).into(), Some(account.clone().into()))].as_mut())
                    .unwrap();
            }

            for (address, account) in accounts {
                let read_account = storage_engine
                    .get_account(&mut context, AddressPath::for_address(address))
                    .unwrap();
                assert_eq!(read_account, Some(Account::new(account.nonce, account.balance, EMPTY_ROOT_HASH, account.code_hash)));
            }
        }

        #[test]
        fn fuzz_insert_get_accounts_and_storage(
            accounts in prop::collection::vec(
                (any::<Address>(), any::<Account>(), prop::collection::vec(
                    (any::<B256>(), any::<U256>()),
                    0..5
                )),
                1..100
            ),
        ) {
            let (mut storage_engine, mut context) = create_test_engine(10_000);

            let mut changes = vec![];
            for (address, account, storage) in &accounts {
                changes.push((AddressPath::for_address(*address).into(), Some(account.clone().into())));

                for (key, value) in storage {
                    changes.push((StoragePath::for_address_and_slot(*address, *key).into(), Some((*value).into())));
                }
            }
            storage_engine
                .set_values(&mut context, changes.as_mut())
                .unwrap();

            for (address, account, storage) in accounts {
                let read_account = storage_engine
                    .get_account(&mut context, AddressPath::for_address(address))
                    .unwrap();
                let read_account = read_account.unwrap();
                assert_eq!(read_account.nonce, account.nonce);
                assert_eq!(read_account.balance, account.balance);
                assert_eq!(read_account.code_hash, account.code_hash);

                for (key, value) in storage {
                    let read_storage = storage_engine
                        .get_storage(&mut context, StoragePath::for_address_and_slot(address, key))
                        .unwrap();
                    assert_eq!(read_storage, Some(value));
                }
            }
        }

        #[test]
        fn fuzz_insert_update_accounts(
            account_revisions in prop::collection::vec(
                (any::<Address>(), prop::collection::vec(any::<Account>(), 1..100)),
                1..100
            ),
        ) {
            let (mut storage_engine, mut context) = create_test_engine(10_000);

            let mut revision = 0;
            loop {
                let mut changes = vec![];
                for (address, revisions) in &account_revisions {
                    if revisions.len() > revision {
                        changes.push((AddressPath::for_address(*address).into(), Some(revisions[revision].clone().into())));
                    }
                }
                if changes.is_empty() {
                    break;
                }
                storage_engine
                    .set_values(&mut context, changes.as_mut())
                    .unwrap();
                revision += 1;
            }

            for (address, revisions) in &account_revisions {
                let last_revision = revisions.last().unwrap();
                let read_account = storage_engine
                    .get_account(&mut context, AddressPath::for_address(*address))
                    .unwrap();
                let read_account = read_account.unwrap();
                assert_eq!(read_account.nonce, last_revision.nonce);
                assert_eq!(read_account.balance, last_revision.balance);
                assert_eq!(read_account.code_hash, last_revision.code_hash);
            }
        }

        #[test]
        fn fuzz_find_shortest_common_prefix(
            mut changes in prop::collection::vec(
                (any::<Nibbles>(), any::<bool>()),
                1..10
            ),
            node in any::<Node>(),
        ) {
            changes.sort_by(|a, b| a.0.cmp(&b.0));
            let (idx, shortest_common_prefix_length) = find_shortest_common_prefix(&changes, 0, &node);
            assert!(idx == 0 || idx == changes.len() - 1, "the shortest common prefix must be found at either end of the changes list");

            let shortest_from_full_iteration = changes.iter().map(|(path, _)| nybbles::common_prefix_length(path, node.prefix())).min().unwrap();

            assert_eq!(shortest_common_prefix_length, shortest_from_full_iteration);
        }
    }
}
