use crate::{
    account::Account,
    database::TransactionContext,
    location::Location,
    node::{Node, TrieValue},
    page::{
        OrphanPageManager, Page, PageError, PageId, PageManager, RootPage, SlottedPage,
        CELL_POINTER_SIZE, PAGE_DATA_SIZE, RO, RW,
    },
    path::{AddressPath, StoragePath},
    pointer::Pointer,
    snapshot::SnapshotId,
};
use alloy_primitives::StorageValue;
use alloy_trie::{Nibbles, EMPTY_ROOT_HASH};
use std::{
    cmp::max,
    fmt::Debug,
    sync::{Arc, RwLock},
};

use super::value::Value;

#[derive(Debug)]
pub struct StorageEngine<P: PageManager> {
    inner: Arc<RwLock<Inner<P>>>,
}

#[derive(Debug)]
struct Inner<P: PageManager> {
    page_manager: P,
    orphan_manager: OrphanPageManager,
    status: Status,
}

#[derive(Debug)]
enum Status {
    Open,
    Closed,
}

impl<P: PageManager> StorageEngine<P> {
    pub fn new(page_manager: P, orphan_manager: OrphanPageManager) -> Self {
        Self {
            inner: Arc::new(RwLock::new(Inner {
                page_manager,
                orphan_manager,
                status: Status::Open,
            })),
        }
    }

    pub(crate) fn unlock(&self, snapshot_id: SnapshotId) {
        let mut inner = self.inner.write().unwrap();

        if inner.is_closed() {
            return;
        }

        inner.orphan_manager.unlock(snapshot_id);
    }

    // Allocates a new page from the underlying page manager.
    // If there is an orphaned page available as of the given snapshot id,
    // it is used to allocate a new page instead.
    fn allocate_page<'p>(&self, context: &mut TransactionContext) -> Result<Page<'p, RW>, Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        inner.allocate_page(context)
    }

    // Retrieves a mutable clone of a page from the underlying page manager.
    // The original page is marked as orphaned and a new page is allocated, potentially from an orphaned page.
    fn get_mut_clone<'p>(
        &self,
        context: &mut TransactionContext,
        page_id: PageId,
    ) -> Result<Page<'p, RW>, Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        let original_page = inner.get_page_mut(context, page_id)?;

        // println!("from snapshot {} to {}", original_page.snapshot_id(), context.metadata.snapshot_id);

        // if the page already has the correct snapshot id, return it without cloning.
        if original_page.snapshot_id() == context.metadata.snapshot_id {
            return Ok(original_page);
        }

        let mut new_page = inner.allocate_page(context)?;

        inner
            .orphan_manager
            .add_orphaned_page_id(context.metadata.snapshot_id, page_id);
        new_page
            .contents_mut()
            .copy_from_slice(original_page.contents());
        Ok(new_page)
    }

    fn get_page<'p>(
        &self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<Page<'p, RO>, Error> {
        let inner = self.inner.read().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        inner.get_page(context, page_id)
    }

    #[cfg(test)]
    fn get_mut_page<'p>(
        &self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<Page<'p, RW>, Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        inner.get_page_mut(context, page_id)
    }

    pub fn get_account(
        &self,
        context: &TransactionContext,
        address_path: AddressPath,
    ) -> Result<Option<Account>, Error> {
        let page = self.get_page(context, context.metadata.root_subtrie_page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;

        match self.get_value_from_page(context, address_path.into(), slotted_page, 0)? {
            Some(TrieValue::Account(account)) => Ok(Some(account)),
            _ => Ok(None),
        }
    }

    fn get_value_from_page(
        &self,
        context: &TransactionContext,
        path: Nibbles,
        slotted_page: SlottedPage<'_, RO>,
        page_index: u8,
    ) -> Result<Option<TrieValue>, Error> {
        let node: Node = slotted_page.get_value(page_index)?;

        let common_prefix_length = path.common_prefix_length(node.prefix());
        if common_prefix_length < node.prefix().len() {
            return Ok(None);
        }

        let remaining_path = path.slice(common_prefix_length..);
        if remaining_path.is_empty() {
            return Ok(Some(node.value()));
        }

        let child_pointer = if !node.is_branch() {
            node.direct_child()
        } else {
            node.child(remaining_path[0])
        };

        let remaining_path = if !node.is_branch() {
            // if we are at an AccountLeaf, we need a "free hop" to the storage trie
            // so the remaining_path needs to contain the current nibble.
            path.slice(common_prefix_length..)
        } else {
            path.slice(common_prefix_length + 1..)
        };

        match child_pointer {
            Some(child_pointer) => {
                let child_location = child_pointer.location();
                if child_location.cell_index().is_some() {
                    self.get_value_from_page(
                        context,
                        remaining_path,
                        slotted_page,
                        child_location.cell_index().unwrap(),
                    )
                } else {
                    let child_page_id = child_location.page_id().unwrap();
                    let child_page = self.get_page(context, child_page_id)?;
                    let child_slotted_page = SlottedPage::try_from(child_page)?;
                    self.get_value_from_page(context, remaining_path, child_slotted_page, 0)
                }
            }
            None => Ok(None),
        }
    }

    pub fn set_accounts(
        &self,
        context: &mut TransactionContext,
        account_changes: impl IntoIterator<Item = (AddressPath, Option<Account>)>,
    ) -> Result<(), Error> {
        self.set_values(
            context,
            account_changes
                .into_iter()
                .map(|(path, value)| (path.into(), value.map(TrieValue::Account)))
                .collect::<Vec<(Nibbles, Option<TrieValue>)>>()
                .as_mut(),
        )
    }

    pub fn set_storage(
        &self,
        context: &mut TransactionContext,
        storage_changes: impl IntoIterator<Item = (StoragePath, Option<StorageValue>)>,
    ) -> Result<(), Error> {
        self.set_values(
            context,
            storage_changes
                .into_iter()
                .map(|(path, value)| (path.full_path(), value.map(TrieValue::Storage)))
                .collect::<Vec<(Nibbles, Option<TrieValue>)>>()
                .as_mut(),
        )
    }

    pub fn set_values(
        &self,
        context: &mut TransactionContext,
        changes: &mut [(Nibbles, Option<TrieValue>)],
    ) -> Result<(), Error> {
        changes.sort_by(|a, b| a.0.cmp(&b.0));
        let pointer =
            self.set_values_in_page(context, changes, 0, context.metadata.root_subtrie_page_id)?;
        match pointer {
            Some(pointer) => {
                context.metadata.root_subtrie_page_id = pointer.location().page_id().unwrap();
                context.metadata.state_root = pointer.rlp().as_hash().unwrap();
            }
            None => {
                context.metadata.root_subtrie_page_id = self.allocate_page(context)?.page_id();
                context.metadata.state_root = EMPTY_ROOT_HASH;
            }
        }
        Ok(())
    }
    fn set_values_in_page(
        &self,
        context: &mut TransactionContext,
        changes: &[(Nibbles, Option<TrieValue>)],
        path_offset: u8,
        page_id: PageId,
    ) -> Result<Option<Pointer>, Error> {
        // println!("set_values_in_page: {:?}", changes);
        let page = self.get_mut_clone(context, page_id)?;
        // println!("cloned page {} to {}", page_id, page.page_id());
        let mut new_slotted_page = SlottedPage::try_from(page)?;
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
                // This case means the root node was deleted so orphan this page
                Ok(None) => {
                    self.inner
                        .write()
                        .unwrap()
                        .orphan_manager
                        .add_orphaned_page_id(context.metadata.snapshot_id, page_id);
                    return Ok(None);
                }
                Ok(pointer) => return Ok(pointer),
                // In the case of a page split, re-attempt the operation from scratch. This ensures that a page will be
                // consistently evaluated, and not modified in the middle of an operation, which could result in
                // inconsistent cell pointers.
                Err(Error::PageSplit) => {
                    context.transaction_metrics.inc_pages_split();
                    split_count += 1;
                    // FIXME: this is a temporary limit to prevent infinite loops.
                    if split_count > 20 {
                        panic!("Page split limit reached!");
                    }
                }
                Err(Error::PageError(PageError::PageIsFull)) => {
                    panic!("Page is full!");
                }
                Err(e) => return Err(e),
            }
        }
    }

    fn set_values_in_cloned_page(
        &self,
        context: &mut TransactionContext,
        changes: &[(Nibbles, Option<TrieValue>)],
        path_offset: u8,
        slotted_page: &mut SlottedPage<'_, RW>,
        page_index: u8,
    ) -> Result<Option<Pointer>, Error> {
        // println!("set_values_in_cloned_page: {:?}", changes);
        let res = slotted_page.get_value::<Node>(page_index);
        if res.is_err() {
            // println!("res is err: {:?}", res);
            // Trie is empty, insert the new account at the root.
            let ((path, value), changes) = changes.split_first().unwrap();
            let path = path.slice(path_offset as usize..);
            let value = value.as_ref().expect("unable to delete from empty trie");
            let new_node = Node::new_leaf(path, value);
            let rlp_node = new_node.rlp_encode();

            // println!("inserting new root node: {:?}", new_node);
            let index = slotted_page.insert_value(&new_node)?;
            assert_eq!(index, 0, "root node must be at index 0");

            if changes.is_empty() {
                return Ok(Some(Pointer::new(
                    Location::for_page(slotted_page.page_id()),
                    rlp_node,
                )));
            } else {
                // recurse with the remaining changes.
                return self.set_values_in_cloned_page(
                    context,
                    changes,
                    path_offset,
                    slotted_page,
                    page_index,
                );
            }
        }

        let mut node = res.unwrap();

        // find the shortest common prefix between the node path and the changes.
        // all changes with this common prefix will be applied together.
        // the remaining changes will be applied in the next iteration.
        let (mut shortest_common_prefix_length, mut shortest_common_prefix_idx) = (usize::MAX, 0);
        for (idx, (path, _)) in changes.iter().enumerate() {
            let path = path.slice(path_offset as usize..);
            let common_prefix_length = path.common_prefix_length(node.prefix());
            if common_prefix_length < shortest_common_prefix_length {
                shortest_common_prefix_length = common_prefix_length;
                shortest_common_prefix_idx = idx;
            }
        }
        let first_change = &changes[shortest_common_prefix_idx];

        let path = first_change.0.slice(path_offset as usize..);
        let value = first_change.1.as_ref();
        let common_prefix_length = path.common_prefix_length(node.prefix());
        // find the common prefix between the path and the node prefix.
        let common_prefix = path.slice(0..common_prefix_length);

        // println!("set_value_in_node: {:?}", node);
        // println!("path: {:?}", path);
        // println!("common_prefix: {:?}", common_prefix);

        if common_prefix_length < node.prefix().len() {
            // the path does not match the node prefix, so we need to create a new branch node as its parent.
            // ensure that the page has enough space (1000 bytes) to insert a new branch and leaf node.
            // TODO: use a more accurate threshold
            if slotted_page.num_free_bytes() < 1000 {
                self.split_page(context, slotted_page)?;
                return Err(Error::PageSplit);
            }
            let mut new_parent_branch = Node::new_branch(common_prefix);
            // update the prefix of the existing node and insert it into the page
            let node_branch_index = node.prefix()[common_prefix_length];
            node.set_prefix(node.prefix().slice(common_prefix_length + 1..));
            let rlp_node = node.rlp_encode();
            let location = Location::for_cell(slotted_page.insert_value(&node)?);
            new_parent_branch.set_child(node_branch_index, Pointer::new(location, rlp_node));

            // no need to compute this yet, as we still need to insert the matching changes into other child slots.
            // let rlp_branch_node = new_parent_branch.rlp_encode();
            slotted_page.set_value(page_index, &new_parent_branch)?;

            // insert the changes into the new branch via recursion
            // println!("inserting changes into new branch: {:?}", changes);
            return self.set_values_in_cloned_page(
                context,
                changes,
                path_offset,
                slotted_page,
                page_index,
            );
        }

        // println!("common_prefix_length: {}, path_len: {}", common_prefix_length, path.len());

        if common_prefix_length == path.len() {
            // assert!(shortest_common_prefix_changes.is_empty(), "only one change is expected to match the node prefix exactly");
            // the path matches the node prefix exactly, so we can update the value.
            if value.is_none() {
                // println!("deleting node at ({}, {}): {:?}", slotted_page.page_id(), page_index, node);
                // we've arrived at the node we need to delete from the slotted page.
                if node.has_children() {
                    // println!("deleting subtrie at page index: {:?}", page_index);
                    // delete our entire subtrie. For example, if this an AccountLeaf
                    // we want to delete all of our storage.
                    self.delete_subtrie(context, slotted_page, page_index)?;
                }

                // println!("deleting value at page index: {:?}", page_index);
                slotted_page.delete_value(page_index)?;

                // println!("remaining changes: {:?}", changes);
                if changes.len() == 1 {
                    return Ok(None);
                }

                // otherwise recurse with remaining changes
                return self.set_values_in_cloned_page(
                    context,
                    &changes[1..],
                    path_offset + common_prefix_length as u8,
                    slotted_page,
                    page_index,
                );
            }
            let new_node = Node::new_leaf(path, value.unwrap());
            let rlp_node = new_node.rlp_encode();
            slotted_page.set_value(page_index, &new_node)?;

            let (left, right) = changes.split_at(shortest_common_prefix_idx);
            let right = &right[1..];

            if left.is_empty() && right.is_empty() {
                return Ok(Some(Pointer::new(
                    self.node_location(slotted_page.page_id(), page_index),
                    rlp_node,
                )));
            } else if left.is_empty() {
                // recurse with the remaining changes.
                // take items to the left of the shortest common prefix.
                return self.set_values_in_cloned_page(
                    context,
                    right,
                    path_offset + common_prefix_length as u8,
                    slotted_page,
                    page_index,
                );
            } else if right.is_empty() {
                // recurse with the remaining changes.
                // take items to the right of the shortest common prefix.
                return self.set_values_in_cloned_page(
                    context,
                    left,
                    path_offset + common_prefix_length as u8,
                    slotted_page,
                    page_index,
                );
            } else {
                // recurse with the remaining changes.
                self.set_values_in_cloned_page(
                    context,
                    left,
                    path_offset + common_prefix_length as u8,
                    slotted_page,
                    page_index,
                )?;

                return self.set_values_in_cloned_page(
                    context,
                    right,
                    path_offset + common_prefix_length as u8,
                    slotted_page,
                    page_index,
                );
            }
        }

        if !node.is_branch() {
            // We are at an AccountLeaf and need to continue traversing the storage trie.
            let child_pointer = node.direct_child();
            if let Some(child_pointer) = child_pointer {
                if let Some(child_cell_index) = child_pointer.location().cell_index() {
                    // println!("traversing LOCAL child node at index: {:?}", child_cell_index);
                    let new_child_pointer = self.set_values_in_cloned_page(
                        context,
                        changes,
                        path_offset + common_prefix_length as u8,
                        slotted_page,
                        child_cell_index,
                    )?;
                    if let Some(new_child_pointer) = new_child_pointer {
                        node.set_child(0, new_child_pointer);
                    } else {
                        node.remove_child(0);
                    }

                    let rlp_node = node.rlp_encode();
                    slotted_page.set_value(page_index, &node)?;

                    return Ok(Some(Pointer::new(
                        self.node_location(slotted_page.page_id(), page_index),
                        rlp_node,
                    )));
                } else {
                    let child_page_id = child_pointer.location().page_id().unwrap();
                    // println!("traversing REMOTE child node at index: {:?}", child_page_id);
                    let new_child_pointer = self.set_values_in_page(
                        context,
                        changes,
                        path_offset + common_prefix_length as u8,
                        child_page_id,
                    )?;
                    if let Some(new_child_pointer) = new_child_pointer {
                        node.set_child(0, new_child_pointer);
                    } else {
                        node.remove_child(0);
                    }

                    let rlp_node = node.rlp_encode();
                    slotted_page.set_value(page_index, &node)?;

                    return Ok(Some(Pointer::new(
                        self.node_location(slotted_page.page_id(), page_index),
                        rlp_node,
                    )));
                }
            } else {
                // the account has no storage trie yet, so we need to create a new leaf node for the first slot
                let node_size_incr = node.size_incr_with_new_child();
                let remaining_path = path.slice(common_prefix_length..);
                let new_node = Node::new_leaf(remaining_path, value.unwrap());

                // if the page doesn't have enough space to
                // 1. insert the new leaf node
                // 2. and the node (branch) size increase
                // 3. and add new cell pointer for the new leaf node (3 bytes)
                // when adding the new child, split the page.
                if slotted_page.num_free_bytes()
                    < node_size_incr + new_node.size() + CELL_POINTER_SIZE
                {
                    self.split_page(context, slotted_page)?;
                    return Err(Error::PageSplit);
                }
                let rlp_node = new_node.rlp_encode();
                let location = Location::for_cell(slotted_page.insert_value(&new_node)?);
                node.set_child(0, Pointer::new(location, rlp_node));

                let rlp_node_with_child = node.rlp_encode();
                slotted_page.set_value(page_index, &node)?;

                if changes.is_empty() {
                    return Ok(Some(Pointer::new(
                        self.node_location(slotted_page.page_id(), page_index),
                        rlp_node_with_child,
                    )));
                }

                return self.set_values_in_cloned_page(
                    context,
                    changes,
                    path_offset,
                    slotted_page,
                    page_index,
                );
            }
        }

        assert!(node.is_branch(), "node must be a branch at this point");

        // the node prefix is a strict prefix of the path, so we need to traverse the node's children.
        let mut remaining_changes = changes;
        // println!("partitioning changes: {:?}", remaining_changes);
        for child_index in 0..16 {
            let matching_changes;
            (matching_changes, remaining_changes) =
                remaining_changes.split_at(remaining_changes.partition_point(|(path, _)| {
                    path[path_offset as usize + common_prefix_length] == child_index
                }));
            if matching_changes.is_empty() {
                // println!("no matching changes for child index: {}", child_index);
                continue;
            }
            // println!("idx({}) inserting at child index({}): {:?}", path_offset + common_prefix_length as u8, child_index, matching_changes);

            // we need to fetch the node again, as it may have been modified by the recursive calls.
            // println!("fetching node at index: {}", page_index);
            let child_pointer = node.child(child_index);

            // println!(
            //     "updating index {} for node {:?} with {:?}",
            //     child_index, node, matching_changes
            // );

            match child_pointer {
                Some(child_pointer) => {
                    // the child node exists, so we need to traverse it.
                    let child_location = child_pointer.location();
                    if let Some(child_cell_index) = child_location.cell_index() {
                        // println!("traversing LOCAL child node at index {}: {} -> {:?}\ncurrent node: {:?}", child_index, slotted_page.page_id(), child_cell_index, node);
                        let new_child_pointer = self.set_values_in_cloned_page(
                            context,
                            matching_changes,
                            path_offset + common_prefix_length as u8 + 1,
                            slotted_page,
                            child_cell_index,
                        )?;
                        if let Some(new_child_pointer) = new_child_pointer {
                            node.set_child(child_index, new_child_pointer);
                            // let rlp_node = node.rlp_encode();
                        } else {
                            // println!(
                            //     "removing child at ({}, {}) for node {:?}",
                            //     slotted_page.page_id(), child_index, node
                            // );
                            node.remove_child(child_index);
                        }
                        slotted_page.set_value(page_index, &node)?;

                        // Ok(Pointer::new(
                        //     self.node_location(slotted_page.page_id(), page_index),
                        //     rlp_node,
                        // ))
                    } else {
                        // println!("traversing REMOTE child node at index {}: {} -> {:?}\ncurrent node: {:?}", child_index, slotted_page.page_id(), child_location.page_id().unwrap(), node);
                        // otherwise, insert the new account into the empty child slot.
                        let child_page_id = child_location.page_id().unwrap();
                        let new_child_pointer = self.set_values_in_page(
                            context,
                            matching_changes,
                            path_offset + common_prefix_length as u8 + 1,
                            child_page_id,
                        )?;
                        // println!("new child pointer: {:?}", new_child_pointer);
                        if let Some(new_child_pointer) = new_child_pointer {
                            node.set_child(child_index, new_child_pointer);
                            // let rlp_node = node.rlp_encode();
                        } else {
                            node.remove_child(child_index);
                        }
                        slotted_page.set_value(page_index, &node)?;
                    }
                }
                None => {
                    // the child node does not exist, so we need to create a new leaf node with the remaining path.
                    // ensure that the page has enough space (200 bytes) to insert a new leaf node.
                    // TODO: use a more accurate threshold
                    if slotted_page.num_free_bytes() < 200 {
                        self.split_page(context, slotted_page)?;
                        return Err(Error::PageSplit);
                    }

                    let ((path, value), matching_changes) = matching_changes.split_first().unwrap();
                    let path = path.slice(path_offset as usize + common_prefix_length + 1..);
                    let value = value.as_ref().ok_or_else(|| {
                        Error::Other("attempting to delete value which does not exist".to_string())
                    })?;
                    // println!("inserting new leaf node at index {}: {:?}", child_index, path);
                    let new_node = Node::new_leaf(path, value);
                    let rlp_node = new_node.rlp_encode();
                    let location = Location::for_cell(slotted_page.insert_value(&new_node)?);
                    node.set_child(child_index, Pointer::new(location, rlp_node));

                    // let rlp_node_with_child = node.rlp_encode();
                    slotted_page.set_value(page_index, &node)?;

                    // if there's any more matching changes, we need to recurse, now that this child node is non-empty.
                    if !matching_changes.is_empty() {
                        self.set_values_in_cloned_page(
                            context,
                            matching_changes,
                            path_offset,
                            slotted_page,
                            page_index,
                        )?;
                    }
                }
            }
        }

        // we need to fetch the node again, as it may have been modified by the recursive calls.
        // let node: Node = slotted_page.get_value(page_index)?;
        // println!("updated node: {:?}", node);
        let children = node.enumerate_children();
        if children.is_empty() {
            // delete this node and return None
            // println!("deleting empty branch node");
            slotted_page.delete_value(page_index)?;
            return Ok(None);
        } else if children.len() == 1 {
            // merge this node with its last remaining child
            let (only_child_index, only_child_node_pointer) = children[0];
            let (mut only_child_node, child_slotted_page) =
                if let Some(cell_index) = only_child_node_pointer.location().cell_index() {
                    (slotted_page.get_value::<Node>(cell_index)?, None)
                } else {
                    // the child is located on another page. load the correct slotted page and
                    // get the child.
                    let child_page = self.get_mut_clone(
                        context,
                        only_child_node_pointer
                            .location()
                            .page_id()
                            .expect("page_id should exist"),
                    )?;
                    let child_slotted_page = SlottedPage::try_from(child_page)?;
                    (child_slotted_page.get_value(0)?, Some(child_slotted_page))
                };
            // println!("merging with last remaining child: parent: {:?}, child: {:?}", node, only_child_node);

            let mut new_nibbles = node.prefix().clone();
            new_nibbles.push(only_child_index);
            new_nibbles = new_nibbles.join(only_child_node.prefix());
            // println!("new nibbles: {:?}", new_nibbles);
            only_child_node.set_prefix(new_nibbles);
            let rlp_node = only_child_node.rlp_encode();

            let child_is_in_same_page = child_slotted_page.is_none();

            if child_is_in_same_page {
                // if the child is on the same page as us, delete the child and
                // write it in our cell index. This also handles the corner case
                // were we are the root node of this page.
                let child_cell_index = only_child_node_pointer
                    .location()
                    .cell_index()
                    .expect("cell index should exist");
                slotted_page.delete_value(child_cell_index)?;
                slotted_page.delete_value(page_index)?;

                // println!("merging on same page {}, new node: {:?}", slotted_page.page_id(), only_child_node);

                let only_child_node_index = slotted_page.insert_value(&only_child_node)?;
                // println!("inserted new node at index {} and rlp {:?}", only_child_node_index, rlp_node);
                if page_index == 0 {
                    // adding this just for sanity checks. if we are the root of the page,
                    // we must insert the new node at index 0
                    assert_eq!(only_child_node_index, page_index);
                }

                return Ok(Some(Pointer::new(
                    self.node_location(slotted_page.page_id(), only_child_node_index),
                    rlp_node,
                )));
            }

            // child is stored on another page at the root cell index 0.
            let mut child_slotted_page =
                child_slotted_page.expect("child slotted page should exist");

            let branch_page_id = slotted_page.page_id();

            // in this case our child is the root node of another page.
            // So we will delete ourself, write the new node in the child location
            // and return the child pointer to our parent. if we are a root node,
            // we will also orphan our current page as this means are page is now
            // completely empty.
            //
            // ensure that the page has enough space (200 bytes) to overwrite.
            // TODO: use a more accurate threshold
            if child_slotted_page.num_free_bytes() < 200 {
                self.split_page(context, &mut child_slotted_page)?;
                // Note: we are not returning Error::PageSplit here because
                // we are not splitting the page we are currently traversing,
                // we are splitting on the **child** page.

                // println!("split child page");
            }

            // delete ourself from disk
            slotted_page.delete_value(page_index)?;

            child_slotted_page.set_value(0, &only_child_node)?;

            if page_index == 0 {
                // We are a root node on this page and just deleted ourself
                // in favor of our child. Our page is now orphaned.
                {
                    self.inner
                        .write()
                        .unwrap()
                        .orphan_manager
                        .add_orphaned_page_id(context.metadata.snapshot_id, branch_page_id);
                }
            }

            // println!("merged {} to child page: {:?}", slotted_page.page_id(), child_slotted_page.page_id());

            return Ok(Some(Pointer::new(
                self.node_location(child_slotted_page.page_id(), 0),
                rlp_node,
            )));
        }
        // otherwise we have a normal branch node with multiple children.
        // we just need to update ourself and return ourself upstream.
        let rlp_node = node.rlp_encode();
        // println!("updated node: {:?}", node);
        // println!("rlp_node: {:?}", rlp_node);

        // println!("returning from branch node at page {}: {:?}", slotted_page.page_id(), node);

        Ok(Some(Pointer::new(
            self.node_location(slotted_page.page_id(), page_index),
            rlp_node,
        )))
    }

    fn node_location(&self, page_id: PageId, page_index: u8) -> Location {
        if page_index == 0 {
            Location::for_page(page_id)
        } else {
            Location::for_cell(page_index)
        }
    }

    // Split the page into two, moving the largest immediate subtrie of the root node to a new child page.
    fn split_page(
        &self,
        context: &mut TransactionContext,
        page: &mut SlottedPage<'_, RW>,
    ) -> Result<(), Error> {
        while page.num_free_bytes() < PAGE_DATA_SIZE / 4_usize {
            let child_page = self.allocate_page(context)?;
            let mut child_slotted_page = SlottedPage::try_from(child_page)?;

            let mut root_node: Node = page.get_value(0)?;

            // Find the child with the largest subtrie
            let (largest_child_index, largest_child_pointer) = root_node
                .enumerate_children()
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
                let location =
                    self.move_subtrie_nodes(page, cell_index, &mut child_slotted_page)?;
                assert!(
                    location.page_id().is_some(),
                    "expected subtrie to be moved to a new page"
                );

                // Update the pointer in the root node to point to the new page
                root_node.set_child(
                    largest_child_index,
                    Pointer::new(
                        Location::for_page(child_slotted_page.page_id()),
                        largest_child_pointer.rlp().clone(),
                    ),
                );
                page.set_value(0, &root_node)?;
            }
        }

        Ok(())
    }

    // Helper function to move an entire subtrie from one page to another.
    fn move_subtrie_nodes(
        &self,
        source_page: &mut SlottedPage<'_, RW>,
        root_index: u8,
        target_page: &mut SlottedPage<'_, RW>,
    ) -> Result<Location, Error> {
        let node: Node = source_page.get_value(root_index)?;
        source_page.delete_value(root_index)?;

        let has_children = node.has_children();

        // first insert the node into the new page to secure its location.
        let new_index = target_page.insert_value(&node)?;

        // if the node has no children, we're done.
        if !has_children {
            return Ok(self.node_location(target_page.page_id(), new_index));
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
            let child_ptr = if !updated_node.is_branch() {
                updated_node.direct_child()
            } else {
                updated_node.child(branch_index)
            };
            if let Some(child_ptr) = child_ptr {
                if let Some(child_index) = child_ptr.location().cell_index() {
                    // Recursively move its children
                    let new_location =
                        self.move_subtrie_nodes(source_page, child_index, target_page)?;
                    // update the pointer in the parent node
                    updated_node.set_child(
                        branch_index,
                        Pointer::new(new_location, child_ptr.rlp().clone()),
                    );
                }
            }
        }

        // update the parent node with the new child pointers.
        target_page.set_value(new_index, &updated_node)?;

        Ok(self.node_location(target_page.page_id(), new_index))
    }

    fn delete_subtrie(
        &self,
        context: &mut TransactionContext,
        slotted_page: &mut SlottedPage<'_, RW>,
        cell_index: u8,
    ) -> Result<(), Error> {
        if cell_index == 0 {
            // if we are a root node, deleting ourself will orphan our entire page and
            // all of our descendant pages. Instead of deleting each cell one-by-one
            // we can orphan our entire page, and recursively orphan all our descendant
            // pages as well.
            return self.orphan_subtrie(context, slotted_page.page_id());
        }

        let node: Node = slotted_page.get_value(cell_index)?;

        if node.has_children() {
            let children = node.enumerate_children();

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

    fn orphan_subtrie(&self, context: &mut TransactionContext, page_id: u32) -> Result<(), Error> {
        let page = self.get_page(context, page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;

        let mut orphaned_page_ids = Vec::new();
        self.orphan_subtrie_helper(context, &slotted_page, 0, &mut orphaned_page_ids)?;

        {
            self.inner
                .write()
                .unwrap()
                .orphan_manager
                .add_orphaned_page_ids(context.metadata.snapshot_id, orphaned_page_ids)
        }

        Ok(())
    }

    fn orphan_subtrie_helper(
        &self,
        context: &mut TransactionContext,
        slotted_page: &SlottedPage<'_, RO>,
        cell_index: u8,
        orphan_page_ids: &mut Vec<PageId>,
    ) -> Result<(), Error> {
        let node: Node = slotted_page.get_value(cell_index)?;

        if node.has_children() {
            let children = node.enumerate_children();

            for (_, child_ptr) in children {
                if let Some(cell_index) = child_ptr.location().cell_index() {
                    self.orphan_subtrie_helper(context, slotted_page, cell_index, orphan_page_ids)?;
                } else {
                    // the child is a root of another page, and that child will be
                    // deleted, essentially orphaning that page and all descendants of
                    // that page.
                    let child_page = self.get_page(
                        context,
                        child_ptr.location().page_id().expect("page_id must exist"),
                    )?;
                    let child_slotted_page = SlottedPage::try_from(child_page)?;
                    self.orphan_subtrie_helper(context, &child_slotted_page, 0, orphan_page_ids)?
                }
            }
        }

        if cell_index == 0 {
            orphan_page_ids.push(slotted_page.page_id());
        }

        Ok(())
    }

    pub fn get_storage(
        &self,
        context: &TransactionContext,
        storage_path: StoragePath,
    ) -> Result<Option<StorageValue>, Error> {
        let page = self.get_page(context, context.metadata.root_subtrie_page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;

        match self.get_value_from_page(context, storage_path.full_path(), slotted_page, 0)? {
            Some(TrieValue::Storage(storage_value)) => Ok(Some(storage_value)),
            _ => Ok(None),
        }
    }

    pub fn commit(&self, context: &TransactionContext) -> Result<(), Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        inner.commit(context)
    }

    pub fn rollback(&self, _context: &TransactionContext) -> Result<(), Error> {
        todo!()
    }

    pub fn resize(&mut self, new_page_count: PageId) -> Result<(), Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        inner.resize(new_page_count)
    }

    pub fn size(&self) -> u32 {
        let inner = self.inner.read().unwrap();
        inner.page_manager.size()
    }

    pub fn close(&self, context: &TransactionContext) -> Result<(), Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        // there will always be a minimum of 256 pages (root pages + reserved orphan pages).
        let max_page_count = max(context.metadata.max_page_number, 256);
        // resize the page manager so that we only store the exact amount of pages we need.
        inner.resize(max_page_count)?;
        // commit all outstanding data to disk.
        inner.commit(context)?;
        // mark engine as closed, causing all operations on engine to return an error.
        inner.status = Status::Closed;

        Ok(())
    }
}

// Helper function to count nodes in a subtrie on the given page
fn count_subtrie_nodes(page: &SlottedPage<'_, RW>, root_index: u8) -> Result<u8, Error> {
    let mut count = 1; // Count the root node
    let node: Node = page.get_value(root_index)?;
    if !node.is_branch() {
        return Ok(count);
    }

    // Count child nodes that are in this page
    for (_, child_ptr) in node.enumerate_children() {
        if let Some(child_index) = child_ptr.location().cell_index() {
            count += count_subtrie_nodes(page, child_index)?;
        }
    }

    Ok(count)
}

impl<P: PageManager> Inner<P> {
    fn is_closed(&self) -> bool {
        matches!(self.status, Status::Closed)
    }

    fn allocate_page<'p>(
        &mut self,
        context: &mut TransactionContext,
    ) -> Result<Page<'p, RW>, Error> {
        let orphaned_page_id = self.orphan_manager.get_orphaned_page_id();
        let page_to_return: Page<'p, RW>;
        if let Some(orphaned_page_id) = orphaned_page_id {
            let mut page = self.get_page_mut(context, orphaned_page_id)?;
            page.set_snapshot_id(context.metadata.snapshot_id);
            page.contents_mut().fill(0);
            context.transaction_metrics.inc_pages_reallocated();
            page_to_return = page;
        } else {
            page_to_return = self.page_manager.allocate(context.metadata.snapshot_id)?;
            context.transaction_metrics.inc_pages_allocated();
        }

        context.metadata.max_page_number =
            max(context.metadata.max_page_number, page_to_return.page_id());
        Ok(page_to_return)
    }

    fn resize(&mut self, new_page_count: PageId) -> Result<(), Error> {
        self.page_manager.resize(new_page_count)?;
        Ok(())
    }

    fn commit(&mut self, context: &TransactionContext) -> Result<(), Error> {
        // First commit to ensure all changes are written before writing the new root page.
        self.page_manager.commit(context.metadata.snapshot_id)?;

        let page_mut = self
            .page_manager
            .get_mut(context.metadata.snapshot_id, context.metadata.root_page_id)
            .unwrap();
        // TODO: include the remaining metadata in the new root page.
        let mut new_root_page = RootPage::new(
            page_mut,
            context.metadata.state_root,
            context.metadata.max_page_number,
        );
        let orphaned_page_ids = self.orphan_manager.iter().copied().collect::<Vec<PageId>>();
        let num_orphan_pages_used = self.orphan_manager.get_num_orphan_pages_used();
        self.orphan_manager.reset_num_orphan_pages_used();
        new_root_page
            .add_orphaned_page_ids(
                &orphaned_page_ids,
                num_orphan_pages_used,
                &mut self.page_manager,
            )
            .unwrap();

        // Second commit to ensure the new root page is written to disk.
        self.page_manager.commit(context.metadata.snapshot_id)?;

        Ok(())
    }

    // a wrapper around the page manager get_mut that increments the pages read metric
    fn get_page_mut<'p>(
        &mut self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<Page<'p, RW>, Error> {
        let page = self
            .page_manager
            .get_mut(context.metadata.snapshot_id, page_id)?;
        context.transaction_metrics.inc_pages_read();
        Ok(page)
    }

    // a wrapper around the page manager get that increments the pages read metric
    fn get_page<'p>(
        &self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<Page<'p, RO>, Error> {
        let page = self
            .page_manager
            .get(context.metadata.snapshot_id, page_id)?;
        context.transaction_metrics.inc_pages_read();
        Ok(page)
    }
}

#[derive(Debug)]
pub enum Error {
    PageError(PageError),
    InvalidPath,
    InvalidSnapshotId,
    EngineClosed,
    PageSplit,
    Other(String),
}

impl From<PageError> for Error {
    fn from(error: PageError) -> Self {
        Error::PageError(error)
    }
}

#[cfg(test)]
mod tests {
    use crate::{account::Account, storage::engine::PageError};
    use alloy_primitives::{address, b256, hex, keccak256, Address, StorageKey, B256, U256};
    use alloy_trie::{
        nodes::RlpNode,
        root::{storage_root_unhashed, storage_root_unsorted},
        EMPTY_ROOT_HASH, KECCAK_EMPTY,
    };
    use proptest::prelude::*;
    use rand::{rngs::StdRng, seq::SliceRandom, Rng, RngCore, SeedableRng};

    use super::*;
    use crate::{database::Metadata, page::MmapPageManager};

    fn create_test_engine(
        page_count: u32,
        root_subtrie_page_id: PageId,
    ) -> (StorageEngine<MmapPageManager>, TransactionContext) {
        let manager = MmapPageManager::new_anon(page_count, root_subtrie_page_id + 1).unwrap();
        let orphan_manager = OrphanPageManager::new();
        let metadata = Metadata {
            snapshot_id: 1,
            root_page_id: 0,
            max_page_number: root_subtrie_page_id,
            root_subtrie_page_id,
            state_root: EMPTY_ROOT_HASH,
        };
        let storage_engine = StorageEngine::new(manager, orphan_manager);
        (storage_engine, TransactionContext::new(metadata))
    }

    fn random_test_account(rng: &mut StdRng) -> Account {
        create_test_account(rng.next_u64(), rng.next_u64())
    }

    fn create_test_account(balance: u64, nonce: u64) -> Account {
        Account::new(nonce, U256::from(balance), EMPTY_ROOT_HASH, KECCAK_EMPTY)
    }

    fn assert_metrics(
        context: &TransactionContext,
        pages_read: u32,
        pages_allocated: u32,
        pages_reallocated: u32,
        pages_split: u32,
    ) {
        assert_eq!(
            context.transaction_metrics.get_pages_read(),
            pages_read,
            "unexpected number of pages read"
        );
        assert_eq!(
            context.transaction_metrics.get_pages_allocated(),
            pages_allocated,
            "unexpected number of pages allocated"
        );
        assert_eq!(
            context.transaction_metrics.get_pages_reallocated(),
            pages_reallocated,
            "unexpected number of pages reallocated"
        );
        assert_eq!(
            context.transaction_metrics.get_pages_split(),
            pages_split,
            "unexpected number of pages split"
        );
    }

    #[test]
    fn test_allocate_get_mut_clone() {
        let (storage_engine, mut context) = create_test_engine(10, 1);

        // Initial allocation
        let mut page = storage_engine.allocate_page(&mut context).unwrap();
        assert_eq!(page.page_id(), 2);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 1);
        assert_metrics(&context, 0, 1, 0, 0);

        // mutation
        page.contents_mut()[0] = 123;
        storage_engine.commit(&context).unwrap();

        context = TransactionContext::new(context.metadata.next());

        // reading mutated page
        let page = storage_engine.get_page(&context, 2).unwrap();
        assert_eq!(page.page_id(), 2);
        assert_eq!(page.contents()[0], 123);
        assert_eq!(page.snapshot_id(), 1);
        assert_metrics(&context, 1, 0, 0, 0);

        // cloning a page should allocate a new page and orphan the original page
        let cloned_page = storage_engine.get_mut_clone(&mut context, 2).unwrap();
        assert_eq!(cloned_page.page_id(), 3);
        assert_eq!(cloned_page.contents()[0], 123);
        assert_eq!(cloned_page.snapshot_id(), 2);
        assert_ne!(cloned_page.page_id(), page.page_id());
        assert_metrics(&context, 2, 1, 0, 0);

        // the next allocation should not come from the orphaned page, as the snapshot id is the same as when the page was orphaned
        let page = storage_engine.allocate_page(&mut context).unwrap();
        assert_eq!(page.page_id(), 4);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 2);
        assert_metrics(&context, 2, 2, 0, 0);

        storage_engine.commit(&context).unwrap();
        context = TransactionContext::new(context.metadata.next());

        // the next allocation should not come from the orphaned page, as the snapshot has not been unlocked yet
        let page = storage_engine.allocate_page(&mut context).unwrap();
        assert_eq!(page.page_id(), 5);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 3);
        assert_metrics(&context, 0, 1, 0, 0);

        storage_engine.unlock(3);

        // the next allocation should come from the orphaned page because the snapshot id has increased.
        // The page data should be zeroed out.
        let page = storage_engine.allocate_page(&mut context).unwrap();
        assert_eq!(page.page_id(), 2);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 3);
        assert_metrics(&context, 1, 1, 1, 0);

        // assert that the metadata tracks the largest page number
        assert_eq!(context.metadata.max_page_number, 5);
    }

    #[test]
    fn test_shared_page_mutability() {
        let (storage_engine, context) = create_test_engine(10, 1);

        let page1 = storage_engine.get_page(&context, 1).unwrap();
        assert_eq!(page1.contents()[0], 0);
        assert_metrics(&context, 1, 0, 0, 0);

        let mut page2 = storage_engine.get_mut_page(&context, 1).unwrap();
        page2.contents_mut()[0] = 123;
        assert_metrics(&context, 2, 0, 0, 0);

        storage_engine.commit(&context).unwrap();

        assert_eq!(page1.contents()[0], 123);
        assert_eq!(page2.contents()[0], 123);
        assert_metrics(&context, 2, 0, 0, 0);
    }

    #[test]
    fn test_set_get_account() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(AddressPath::for_address(address), Some(account.clone()))],
            )
            .unwrap();
        assert_eq!(context.metadata.root_subtrie_page_id, 257);
        assert_metrics(&context, 1, 1, 0, 0);

        let test_cases = vec![
            (
                address!("0x4200000000000000000000000000000000000015"),
                create_test_account(123, 456),
            ),
            (
                address!("0x4200000000000000000000000000000000000016"),
                create_test_account(999, 999),
            ),
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

            let read_account = storage_engine.get_account(&context, path.clone()).unwrap();
            assert_eq!(read_account, None);

            storage_engine
                .set_accounts(&mut context, vec![(path, Some(account.clone()))])
                .unwrap();
        }

        // Verify all accounts exist after insertion
        for (address, account) in test_cases {
            let read_account = storage_engine
                .get_account(&context, AddressPath::for_address(address))
                .unwrap();
            assert_eq!(read_account, Some(account));
        }
    }

    #[test]
    fn test_simple_trie_state_root_1() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        let address1 = address!("0x8e64566b5eb8f595f7eb2b8d302f2e5613cb8bae");
        let account1 = create_test_account(1_000_000_000_000_000_000u64, 0);
        let path1 = AddressPath::for_address(address1);

        let address2 = address!("0xcea8f2236efa20c8fadeb9d66e398a6532cca6c8");
        let account2 = create_test_account(14_000_000_000_000_000_000u64, 1);
        let path2 = AddressPath::for_address(address2);

        storage_engine
            .set_accounts(
                &mut context,
                vec![
                    (path1, Some(account1.clone())),
                    (path2, Some(account2.clone())),
                ],
            )
            .unwrap();
        assert_metrics(&context, 1, 1, 0, 0);

        assert_eq!(
            context.metadata.state_root,
            b256!("0x0d9348243d7357c491e6a61f4b1305e77dc6acacdb8cc708e662f6a9bab6ca02")
        );
    }

    #[test]
    fn test_simple_trie_state_root_2() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        let address1 = address!("0x000f3df6d732807ef1319fb7b8bb8522d0beac02");
        let account1 = Account::new(1, U256::from(0), EMPTY_ROOT_HASH, keccak256(hex!("0x3373fffffffffffffffffffffffffffffffffffffffe14604d57602036146024575f5ffd5b5f35801560495762001fff810690815414603c575f5ffd5b62001fff01545f5260205ff35b5f5ffd5b62001fff42064281555f359062001fff015500")));
        let path1 = AddressPath::for_address(address1);

        let address2 = address!("0x0000000000000000000000000000000000001000");
        let account2 = Account::new(1, U256::from(0x010000000000u64), EMPTY_ROOT_HASH, keccak256(hex!("0x366000602037602060003660206000720f3df6d732807ef1319fb7b8bb8522d0beac02620186a0f16000556000516001553d6002553d600060003e600051600355")));
        let path2 = AddressPath::for_address(address2);

        let address3 = address!("0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b");
        let account3 = Account::new(
            0,
            U256::from(0x3635c9adc5dea00000u128),
            EMPTY_ROOT_HASH,
            KECCAK_EMPTY,
        );
        let path3 = AddressPath::for_address(address3);

        storage_engine
            .set_accounts(
                &mut context,
                vec![
                    (path1, Some(account1)),
                    (path2, Some(account2)),
                    (path3, Some(account3)),
                ],
            )
            .unwrap();
        assert_metrics(&context, 1, 1, 0, 0);

        assert_eq!(
            context.metadata.state_root,
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

        let account3_updated = Account::new(
            1,
            U256::from(0x3635c9adc5de938d5cu128),
            EMPTY_ROOT_HASH,
            KECCAK_EMPTY,
        );

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

        storage_engine
            .set_values(&mut context, changes.as_mut())
            .unwrap();
        assert_metrics(&context, 2, 1, 0, 0);

        assert_eq!(
            context.metadata.state_root,
            b256!("0xf869dcb9ef8893f6b30bf495847fd99166aaf790ed962c468d11a826996ab2d2")
        );
    }

    #[test]
    fn test_trie_state_root_order_independence() {
        let mut rng = StdRng::seed_from_u64(1);

        // create 100 accounts with random addresses, balances, and storage values
        let mut accounts = Vec::new();
        for _ in 0..100 {
            let address = Address::random_with(&mut rng);
            let account = random_test_account(&mut rng);
            let mut storage = Vec::new();
            if rng.next_u64() % 10 == 0 {
                for _ in 0..rng.gen_range(1..25) {
                    let slot = StorageKey::random_with(&mut rng);
                    storage.push((slot, StorageValue::from(rng.next_u64())));
                }
            }
            accounts.push((address, account, storage));
        }

        let (storage_engine, mut context) = create_test_engine(350, 256);

        // insert accounts and storage in random order
        accounts.shuffle(&mut rng);
        for (address, account, mut storage) in accounts.clone() {
            storage_engine
                .set_accounts(
                    &mut context,
                    vec![(AddressPath::for_address(address), Some(account))],
                )
                .unwrap();
            storage.shuffle(&mut rng);
            for (slot, value) in storage {
                storage_engine
                    .set_storage(
                        &mut context,
                        vec![(
                            StoragePath::for_address_and_slot(address, slot),
                            Some(value),
                        )],
                    )
                    .unwrap();
            }
        }

        // commit the changes
        storage_engine.commit(&context).unwrap();

        let state_root = context.metadata.state_root;

        let (storage_engine, mut context) = create_test_engine(350, 256);

        // insert accounts in a different random order, but only after inserting different values first
        accounts.shuffle(&mut rng);
        for (address, _, mut storage) in accounts.clone() {
            storage_engine
                .set_accounts(
                    &mut context,
                    vec![(
                        AddressPath::for_address(address),
                        Some(random_test_account(&mut rng)),
                    )],
                )
                .unwrap();

            storage.shuffle(&mut rng);
            for (slot, _) in storage {
                storage_engine
                    .set_storage(
                        &mut context,
                        vec![(
                            StoragePath::for_address_and_slot(address, slot),
                            Some(StorageValue::from(rng.next_u64())),
                        )],
                    )
                    .unwrap();
            }
        }

        accounts.shuffle(&mut rng);
        for (address, account, mut storage) in accounts {
            storage_engine
                .set_accounts(
                    &mut context,
                    vec![(AddressPath::for_address(address), Some(account))],
                )
                .unwrap();

            storage.shuffle(&mut rng);
            for (slot, value) in storage {
                storage_engine
                    .set_storage(
                        &mut context,
                        vec![(
                            StoragePath::for_address_and_slot(address, slot),
                            Some(value),
                        )],
                    )
                    .unwrap();
            }
        }

        // commit the changes
        storage_engine.commit(&context).unwrap();

        // verify the state root is the same
        assert_eq!(state_root, context.metadata.state_root);
    }

    #[test]
    fn test_set_get_account_common_prefix() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

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
                .set_accounts(&mut context, vec![(path, Some(account.clone()))])
                .unwrap();
        }

        // Verify all accounts exist
        for (nibbles, account) in test_accounts {
            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let read_account = storage_engine.get_account(&context, path).unwrap();
            assert_eq!(read_account, Some(account));
        }
    }

    #[test]
    fn test_split_page() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

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
                .set_accounts(&mut context, vec![(path, Some(account.clone()))])
                .unwrap();
        }

        // Split the page
        let page = storage_engine.get_mut_page(&context, 257).unwrap();
        let mut slotted_page = SlottedPage::try_from(page).unwrap();
        storage_engine
            .split_page(&mut context, &mut slotted_page)
            .unwrap();

        // Verify all accounts still exist after split
        for (nibbles, account) in test_accounts {
            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let read_account = storage_engine.get_account(&context, path).unwrap();
            assert_eq!(read_account, Some(account));
        }
    }

    #[test]
    fn test_insert_get_1000_accounts() {
        let (storage_engine, mut context) = create_test_engine(5000, 256);

        for i in 0..1000 {
            let path = address_path_for_idx(i);
            let account = create_test_account(i, i);
            storage_engine
                .set_accounts(&mut context, vec![(path.clone(), Some(account.clone()))])
                .unwrap();

            context.metadata.snapshot_id += 1;
        }

        for i in 0..1000 {
            let path = address_path_for_idx(i);
            let account = storage_engine.get_account(&context, path.clone()).unwrap();
            assert_eq!(account, Some(create_test_account(i, i)));
        }
    }

    #[test]
    #[should_panic]
    fn test_set_storage_slot_with_no_account_panics() {
        let (storage_engine, mut context) = create_test_engine(300, 256);
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");

        let storage_key =
            b256!("0x0000000000000000000000000000000000000000000000000000000000000000");
        let storage_value =
            b256!("0x0000000000000000000000000000000000000000000000000000000062617365");

        let storage_path = StoragePath::for_address_and_slot(address, storage_key);

        let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

        storage_engine
            .set_storage(&mut context, vec![(storage_path, Some(storage_value))])
            .unwrap();
    }

    #[test]
    fn test_set_get_account_storage_slots() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(AddressPath::for_address(address), Some(account.clone()))],
            )
            .unwrap();
        assert_eq!(context.metadata.root_subtrie_page_id, 257);

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
            let read_storage_slot = storage_engine
                .get_storage(&context, storage_path.clone())
                .unwrap();
            assert_eq!(read_storage_slot, None);
        }

        storage_engine
            .set_storage(
                &mut context,
                test_cases.iter().map(|(key, value)| {
                    let storage_path = StoragePath::for_address_and_slot(address, *key);
                    let storage_value = StorageValue::from_be_slice(value.as_slice());
                    (storage_path, Some(storage_value))
                }),
            )
            .unwrap();
        context.metadata = context.metadata.next();

        // Verify all storage slots exist after insertion
        for (storage_key, storage_value) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);
            let read_storage_slot = storage_engine.get_storage(&context, storage_path).unwrap();
            let storage_value = StorageValue::from_be_slice(storage_value.as_slice());
            assert_eq!(read_storage_slot, Some(storage_value));
        }
    }

    #[test]
    fn test_set_get_account_storage_roots() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(AddressPath::for_address(address), Some(account.clone()))],
            )
            .unwrap();
        assert_eq!(context.metadata.root_subtrie_page_id, 257);

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

            let read_storage_slot = storage_engine
                .get_storage(&context, storage_path.clone())
                .unwrap();
            assert_eq!(read_storage_slot, None);

            let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

            storage_engine
                .set_storage(&mut context, vec![(storage_path, Some(storage_value))])
                .unwrap();

            context.metadata = context.metadata.next();
        }

        // Verify the storage roots is correct. The storage root should be equivalent to the hash
        // of a trie that was initially empty and then filled with these key/values.
        let expected_root = storage_root_unhashed(test_cases.into_iter().map(|(key, value)| {
            (
                key,
                U256::from_be_bytes::<32>(value.as_slice().try_into().unwrap()),
            )
        }));

        let account = storage_engine
            .get_account(&context, AddressPath::for_address(address))
            .unwrap()
            .unwrap();

        assert_eq!(account.storage_root, expected_root);
    }

    #[test]
    fn test_set_get_many_accounts_storage_roots() {
        let (storage_engine, mut context) = create_test_engine(2000, 256);

        for i in 0..100 {
            let address =
                Address::from_slice(&keccak256((i as u32).to_le_bytes()).as_slice()[0..20]);
            let path = AddressPath::for_address(address);
            let account = create_test_account(i, i);
            storage_engine
                .set_accounts(&mut context, vec![(path.clone(), Some(account.clone()))])
                .unwrap();

            context.metadata.snapshot_id += 1;
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
                    .set_storage(
                        &mut context,
                        vec![(storage_path.clone(), Some(storage_slot_value))],
                    )
                    .unwrap();

                keys_values.push((
                    B256::from_slice(storage_path.get_slot().pack().as_slice()),
                    storage_slot_value,
                ))
            }

            // println!("checking storage root!!!");
            let expected_root = storage_root_unsorted(keys_values.into_iter());

            // check the storage root of the account
            let account = storage_engine.get_account(&context, path).unwrap().unwrap();

            assert_eq!(account.storage_root, expected_root);
        }
    }

    #[test]
    fn test_split_page_stress() {
        // Create a storage engine with limited pages to force splits
        let (storage_engine, mut context) = create_test_engine(5000, 256);

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
            assert!(
                unique_paths.insert(path.clone()),
                "Duplicate path found: {:?}",
                path
            );
        }

        // Insert all accounts
        for (path, account) in &accounts {
            storage_engine
                .set_accounts(&mut context, vec![(path.clone(), Some(account.clone()))])
                .unwrap();
        }

        // Verify all accounts exist with correct values
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine.get_account(&context, path.clone()).unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "Account mismatch for path: {:?}",
                path
            );
        }

        // Force multiple splits to stress the system
        // Find all pages in the trie and split them recursively
        let mut pages_to_split = vec![context.metadata.root_subtrie_page_id];
        while let Some(page_id) = pages_to_split.pop() {
            let page_result = storage_engine.get_mut_page(&context, page_id);
            if matches!(
                page_result,
                Err(Error::PageError(PageError::PageNotFound(_)))
            ) {
                break;
            }
            let mut slotted_page = SlottedPage::try_from(page_result.unwrap()).unwrap();

            // Try to split this page
            if storage_engine
                .split_page(&mut context, &mut slotted_page)
                .is_ok()
            {
                // If split succeeded, add the new pages to be processed
                pages_to_split.push(page_id + 1); // New page created by split
            }
        }

        // Verify all accounts still exist with correct values after splits
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine.get_account(&context, path.clone()).unwrap();
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
            .set_accounts(
                &mut context,
                additional_accounts
                    .iter()
                    .map(|(path, account)| (path.clone(), Some(account.clone()))),
            )
            .unwrap();

        // Verify all original accounts still exist
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine.get_account(&context, path.clone()).unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "Original account lost after adding new accounts"
            );
        }

        // Verify all new accounts exist
        for (path, expected_account) in &additional_accounts {
            let retrieved_account = storage_engine.get_account(&context, path.clone()).unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "New account not found"
            );
        }
        // Verify the pages split metric
        assert!(context.transaction_metrics.get_pages_split() > 0);
    }

    #[test]
    fn test_split_page_random_accounts() {
        use rand::{rngs::StdRng, Rng, SeedableRng};

        // Create a storage engine
        let (storage_engine, mut context) = create_test_engine(2000, 256);

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
            .set_accounts(
                &mut context,
                accounts
                    .clone()
                    .into_iter()
                    .map(|(path, account)| (path, Some(account))),
            )
            .unwrap();

        // Verify all accounts exist with correct values
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine.get_account(&context, path.clone()).unwrap();
            assert_eq!(retrieved_account, Some(expected_account.clone()));
        }

        // Get all pages and force splits on them
        let mut page_ids = Vec::new();
        // Start with the root page
        page_ids.push(context.metadata.root_subtrie_page_id);

        // Process each page
        for i in 0..page_ids.len() {
            let page_id = page_ids[i];

            // Try to get and split the page
            if let Ok(page) = storage_engine.get_mut_page(&context, page_id) {
                if let Ok(mut slotted_page) = SlottedPage::try_from(page) {
                    // Force a split
                    let _ = storage_engine.split_page(&mut context, &mut slotted_page);

                    // Get the node to find child pages
                    if let Ok(node) = slotted_page.get_value::<Node>(0) {
                        // Add child pages to our list
                        for (_, child_ptr) in node.enumerate_children() {
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
            let retrieved_account = storage_engine.get_account(&context, path.clone()).unwrap();
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
                .set_accounts(
                    &mut context,
                    vec![(path.clone(), Some(new_account.clone()))],
                )
                .unwrap();

            // Update in our test data
            accounts[*idx] = (path.clone(), new_account.clone());
        }

        // Verify all accounts have correct values after updates
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine.get_account(&context, path.clone()).unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "Account mismatch after updates"
            );
        }
    }

    #[test]
    fn test_delete_account() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(AddressPath::for_address(address), Some(account.clone()))],
            )
            .unwrap();
        assert_metrics(&context, 1, 1, 0, 0);

        // Check that the account exists
        let read_account = storage_engine
            .get_account(&context, AddressPath::for_address(address))
            .unwrap();
        assert_eq!(read_account, Some(account.clone()));

        // Reset the context metrics
        let mut context = TransactionContext::new(context.metadata);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(AddressPath::for_address(address), None)],
            )
            .unwrap();
        assert_metrics(&context, 2, 1, 0, 0);

        // Verify the account is deleted
        let read_account = storage_engine.get_account(&context, AddressPath::for_address(address));
        // The error is an InvalidCellPointer error, and not None
        // TODO: does it make sense to have an error here?
        assert!(read_account.is_err());
    }

    #[test]
    fn test_delete_accounts() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(AddressPath::for_address(address), Some(account.clone()))],
            )
            .unwrap();
        assert_eq!(context.metadata.root_subtrie_page_id, 257);

        let test_cases = vec![
            (
                address!("0x4200000000000000000000000000000000000015"),
                create_test_account(123, 456),
            ),
            (
                address!("0x4200000000000000000000000000000000000016"),
                create_test_account(999, 999),
            ),
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

            let read_account = storage_engine.get_account(&context, path.clone()).unwrap();
            assert_eq!(read_account, None);

            storage_engine
                .set_accounts(&mut context, vec![(path, Some(account.clone()))])
                .unwrap();
        }

        // Verify all accounts exist after insertion
        for (address, account) in &test_cases {
            let read_account = storage_engine
                .get_account(&context, AddressPath::for_address(*address))
                .unwrap();
            assert_eq!(read_account, Some(account.clone()));
        }

        // Delete all accounts
        for (address, _) in &test_cases {
            storage_engine
                .set_accounts(
                    &mut context,
                    vec![(AddressPath::for_address(*address), None)],
                )
                .unwrap();
        }

        // Verify that the accounts don't exist anymore
        for (address, _) in &test_cases {
            let read_account = storage_engine
                .get_account(&context, AddressPath::for_address(*address))
                .unwrap();
            assert_eq!(read_account, None);
        }
    }

    #[test]
    fn test_some_delete_accounts() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(AddressPath::for_address(address), Some(account.clone()))],
            )
            .unwrap();
        assert_eq!(context.metadata.root_subtrie_page_id, 257);

        let test_cases = vec![
            (
                address!("0x4200000000000000000000000000000000000015"),
                create_test_account(123, 456),
            ),
            (
                address!("0x4200000000000000000000000000000000000016"),
                create_test_account(999, 999),
            ),
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

            let read_account = storage_engine.get_account(&context, path.clone()).unwrap();
            assert_eq!(read_account, None);

            storage_engine
                .set_accounts(&mut context, vec![(path, Some(account.clone()))])
                .unwrap();
        }

        // Verify all accounts exist after insertion
        for (address, account) in &test_cases {
            let read_account = storage_engine
                .get_account(&context, AddressPath::for_address(*address))
                .unwrap();
            assert_eq!(read_account, Some(account.clone()));
        }

        // Delete only a portion of the accounts
        for (address, _) in &test_cases[0..2] {
            storage_engine
                .set_accounts(
                    &mut context,
                    vec![(AddressPath::for_address(*address), None)],
                )
                .unwrap();
        }

        // Verify that the accounts don't exist anymore
        for (address, _) in &test_cases[0..2] {
            let read_account = storage_engine
                .get_account(&context, AddressPath::for_address(*address))
                .unwrap();
            assert_eq!(read_account, None);
        }

        // Verify that the non-deleted accounts still exist
        for (address, account) in &test_cases[2..] {
            let read_account = storage_engine
                .get_account(&context, AddressPath::for_address(*address))
                .unwrap();
            assert_eq!(read_account, Some(account.clone()));
        }
    }

    #[test]
    fn test_delete_storage() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(AddressPath::for_address(address), Some(account.clone()))],
            )
            .unwrap();
        assert_eq!(context.metadata.root_subtrie_page_id, 257);

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

            let read_storage_slot = storage_engine
                .get_storage(&context, storage_path.clone())
                .unwrap();
            assert_eq!(read_storage_slot, None);

            let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

            storage_engine
                .set_storage(&mut context, vec![(storage_path, Some(storage_value))])
                .unwrap();

            context = TransactionContext::new(context.metadata.next());
        }

        // Verify that we get all the storage values
        for (storage_key, storage_value) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

            let read_storage_slot = storage_engine
                .get_storage(&context, storage_path.clone())
                .unwrap();
            assert_eq!(read_storage_slot, Some(storage_value));
        }

        // Verify our storage root with alloy
        let mut keys_values: Vec<(B256, U256)> = test_cases
            .clone()
            .into_iter()
            .map(|(key, value)| {
                (
                    key,
                    U256::from_be_bytes::<32>(value.as_slice().try_into().unwrap()),
                )
            })
            .collect();
        let expected_root = storage_root_unhashed(keys_values.clone());
        let account = storage_engine
            .get_account(&context, AddressPath::for_address(address))
            .unwrap()
            .unwrap();

        assert_eq!(account.storage_root, expected_root);

        // Delete storage one at a time
        for (storage_key, _) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            storage_engine
                .set_storage(&mut context, vec![(storage_path.clone(), None)])
                .unwrap();

            let read_storage_slot = storage_engine
                .get_storage(&context, storage_path.clone())
                .unwrap();

            assert_eq!(read_storage_slot, None);

            // check that the storage root is consistent
            keys_values.remove(0);
            let expected_root = storage_root_unhashed(keys_values.clone());
            let account = storage_engine
                .get_account(&context, AddressPath::for_address(address))
                .unwrap()
                .unwrap();

            assert_eq!(account.storage_root, expected_root);
        }
    }

    #[test]
    fn test_delete_account_also_deletes_storage() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(AddressPath::for_address(address), Some(account.clone()))],
            )
            .unwrap();
        assert_eq!(context.metadata.root_subtrie_page_id, 257);

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

            let read_storage_slot = storage_engine
                .get_storage(&context, storage_path.clone())
                .unwrap();
            assert_eq!(read_storage_slot, None);

            let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

            storage_engine
                .set_storage(&mut context, vec![(storage_path, Some(storage_value))])
                .unwrap();

            context = TransactionContext::new(context.metadata.next());
        }

        // Verify that we get all the storage values
        for (storage_key, storage_value) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

            let read_storage_slot = storage_engine
                .get_storage(&context, storage_path.clone())
                .unwrap();
            assert_eq!(read_storage_slot, Some(storage_value));
        }

        // Delete the account
        storage_engine
            .set_accounts(
                &mut context,
                vec![(AddressPath::for_address(address), None)],
            )
            .unwrap();

        // Verify the account no longer exists
        let res = storage_engine.get_account(&context, AddressPath::for_address(address));
        // println!("res: {:?}", res);
        assert!(matches!(
            res,
            Err(Error::PageError(PageError::InvalidCellPointer))
        ));

        // Verify all the storage slots don't exist
        for (storage_key, _) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            let res = storage_engine.get_storage(&context, storage_path.clone());
            assert!(matches!(
                res,
                Err(Error::PageError(PageError::InvalidCellPointer))
            ));
        }

        // Now create a new account with the same address again and set storage
        storage_engine
            .set_accounts(
                &mut context,
                vec![(AddressPath::for_address(address), Some(account.clone()))],
            )
            .unwrap();

        // Verify all the storage slots still don't exist
        for (storage_key, _) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

            let read_storage = storage_engine
                .get_storage(&context, storage_path.clone())
                .unwrap();
            assert_eq!(read_storage, None);
        }
    }

    #[test]
    fn test_delete_single_child_branch_on_same_page() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        // GIVEN: a branch node with 2 children, where all the children live on the same page
        let mut account_1_nibbles = [0u8; 64];
        account_1_nibbles[0] = 1;

        let mut account_2_nibbles = [0u8; 64];
        account_2_nibbles[0] = 11;

        let account1 = create_test_account(100, 1);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(
                    AddressPath::new(Nibbles::from_nibbles(account_1_nibbles)),
                    Some(account1.clone()),
                )],
            )
            .unwrap();

        let account2 = create_test_account(101, 2);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(
                    AddressPath::new(Nibbles::from_nibbles(account_2_nibbles)),
                    Some(account2.clone()),
                )],
            )
            .unwrap();
        assert_eq!(context.metadata.root_subtrie_page_id, 257);

        let page = storage_engine
            .get_page(&context, context.metadata.root_subtrie_page_id)
            .unwrap();
        let slotted_page = SlottedPage::try_from(page).unwrap();
        let node: Node = slotted_page.get_value(0).unwrap();
        assert!(node.is_branch());

        // WHEN: one of these accounts is deleted
        storage_engine
            .set_accounts(
                &mut context,
                vec![(
                    AddressPath::new(Nibbles::from_nibbles(account_1_nibbles)),
                    None,
                )],
            )
            .unwrap();

        // THEN: the root node should be a leaf node containing the remaining account
        //
        // first verify the deleted account is gone and the remaining account exists
        let read_account1 = storage_engine
            .get_account(
                &context,
                AddressPath::new(Nibbles::from_nibbles(account_1_nibbles)),
            )
            .unwrap();
        assert_eq!(read_account1, None);

        let read_account2 = storage_engine
            .get_account(
                &context,
                AddressPath::new(Nibbles::from_nibbles(account_2_nibbles)),
            )
            .unwrap();
        assert_eq!(read_account2, Some(account2));

        // check the the root node is a leaf
        let page = storage_engine
            .get_page(&context, context.metadata.root_subtrie_page_id)
            .unwrap();
        let slotted_page = SlottedPage::try_from(page).unwrap();
        let node: Node = slotted_page.get_value(0).unwrap();
        assert!(!node.is_branch());
    }

    #[test]
    fn test_delete_single_child_non_root_branch_on_different_pages() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        // GIVEN: a non-root branch node with 2 children where both children are on a different pages
        //
        // first we construct a root branch node.
        let mut account_1_nibbles = [0u8; 64];
        account_1_nibbles[0] = 1;

        let mut account_2_nibbles = [0u8; 64];
        account_2_nibbles[0] = 11;

        let account1 = create_test_account(100, 1);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(
                    AddressPath::new(Nibbles::from_nibbles(account_1_nibbles)),
                    Some(account1.clone()),
                )],
            )
            .unwrap();

        let account2 = create_test_account(101, 2);
        storage_engine
            .set_accounts(
                &mut context,
                vec![(
                    AddressPath::new(Nibbles::from_nibbles(account_2_nibbles)),
                    Some(account2.clone()),
                )],
            )
            .unwrap();
        assert_eq!(context.metadata.root_subtrie_page_id, 257);

        let page = storage_engine
            .get_page(&context, context.metadata.root_subtrie_page_id)
            .unwrap();
        let slotted_page = SlottedPage::try_from(page).unwrap();
        let mut root_node: Node = slotted_page.get_value(0).unwrap();
        assert!(root_node.is_branch());

        let test_account = create_test_account(424, 234);

        // next we will force add a branch node in the middle of the root node (index 5)

        // page1 will hold our root node and the branch node
        let page1 = storage_engine
            .get_mut_page(&context, context.metadata.root_subtrie_page_id)
            .unwrap();
        let mut slotted_page1 = SlottedPage::try_from(page1).unwrap();

        // page2 will hold our 1st child
        let page2 = storage_engine.allocate_page(&mut context).unwrap();
        let mut slotted_page2 = SlottedPage::try_from(page2).unwrap();

        // page3 will hold our 2nd child
        let page3 = storage_engine.allocate_page(&mut context).unwrap();
        let mut slotted_page3 = SlottedPage::try_from(page3).unwrap();

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
        );

        let mut child_2_full_path = [0u8; 64];
        child_2_full_path[0] = 5; // root branch nibble
        child_2_full_path[1] = 15; // inner branch nibble
        child_2_full_path[2] = 1; // leaf prefix
        child_2_full_path[3] = 2; // leaf prefix
        child_2_full_path[4] = 3; // leaf prefix
        let child_2: Node = Node::new_leaf(
            Nibbles::from_nibbles(&child_2_full_path[2..]),
            &TrieValue::Account(test_account.clone()),
        );

        // child 1 is the root of page2
        slotted_page2.insert_value(&child_1).unwrap();
        let child_1_location = Location::from(slotted_page2.page_id());

        // child 2 is the root of page3
        slotted_page3.insert_value(&child_2).unwrap();
        let child_2_location = Location::from(slotted_page3.page_id());

        let mut new_branch_node: Node = Node::new_branch(Nibbles::new());
        new_branch_node.set_child(0, Pointer::new(child_1_location, RlpNode::default()));
        new_branch_node.set_child(15, Pointer::new(child_2_location, RlpNode::default()));
        let new_branch_node_index = slotted_page1.insert_value(&new_branch_node).unwrap();
        let new_branch_node_location = Location::from(new_branch_node_index as u32);

        root_node.set_child(
            5,
            Pointer::new(new_branch_node_location, RlpNode::default()),
        );
        slotted_page1.set_value(0, &root_node).unwrap();

        storage_engine.commit(&context).unwrap();

        // assert we can get the child account we just added:
        let child_1_nibbles = Nibbles::from_nibbles(child_1_full_path);
        let child_2_nibbles = Nibbles::from_nibbles(child_2_full_path);
        let read_account1 = storage_engine
            .get_account(&context, AddressPath::new(child_1_nibbles.clone()))
            .unwrap();
        assert_eq!(read_account1, Some(test_account.clone()));
        let read_account2 = storage_engine
            .get_account(&context, AddressPath::new(child_2_nibbles.clone()))
            .unwrap();
        assert_eq!(read_account2, Some(test_account.clone()));

        // WHEN: child 1 is deleted
        let child_1_path = Nibbles::from_nibbles(child_1_full_path);
        storage_engine
            .set_accounts(&mut context, vec![(AddressPath::new(child_1_path), None)])
            .unwrap();

        // THEN: the branch node should be deleted and the root node should go to child 2 leaf at index 5
        let root_node: Node = slotted_page.get_value(0).unwrap();
        assert!(root_node.is_branch());
        let child_2_pointer = root_node.child(5).unwrap();
        assert!(child_2_pointer.location().page_id().is_some());
        assert_eq!(
            child_2_pointer.location().page_id().unwrap(),
            slotted_page3.page_id()
        );

        // check that the prefix for child 2 has changed
        let child_2_node: Node = slotted_page3.get_value(0).unwrap();
        assert!(!child_2_node.is_branch());
        assert_eq!(
            child_2_node.prefix().clone(),
            Nibbles::from_nibbles(&child_2_full_path[1..])
        );

        // test that we can get child 2 and not child 1
        let read_account2 = storage_engine
            .get_account(&context, AddressPath::new(child_2_nibbles))
            .unwrap();
        assert_eq!(read_account2, Some(test_account.clone()));
        let read_account1 = storage_engine
            .get_account(&context, AddressPath::new(child_1_nibbles))
            .unwrap();
        assert_eq!(read_account1, None);
    }

    #[test]
    fn test_delete_single_child_root_branch_on_different_pages() {
        let (storage_engine, mut context) = create_test_engine(300, 256);

        // GIVEN: a root branch node with 2 children where both children are on a different page
        //
        // first we construct our two children on separate pages.
        let test_account = create_test_account(424, 234);

        // page2 will hold our 1st child
        let page2 = storage_engine.allocate_page(&mut context).unwrap();
        let mut slotted_page2 = SlottedPage::try_from(page2).unwrap();

        // page3 will hold our 2nd child
        let page3 = storage_engine.allocate_page(&mut context).unwrap();
        let mut slotted_page3 = SlottedPage::try_from(page3).unwrap();

        // we will force add 2 children to our root node
        let mut child_1_full_path = [0u8; 64];
        child_1_full_path[0] = 0; // root branch nibble
        child_1_full_path[2] = 10; // leaf prefix
        child_1_full_path[3] = 11; // leaf prefix
        child_1_full_path[4] = 12; // leaf prefix
        let child_1: Node = Node::new_leaf(
            Nibbles::from_nibbles(&child_1_full_path[1..]),
            &TrieValue::Account(test_account.clone()),
        );

        let mut child_2_full_path = [0u8; 64];
        child_2_full_path[0] = 15; // root branch nibble
        child_2_full_path[2] = 1; // leaf prefix
        child_2_full_path[3] = 2; // leaf prefix
        child_2_full_path[4] = 3; // leaf prefix
        let child_2: Node = Node::new_leaf(
            Nibbles::from_nibbles(&child_2_full_path[1..]),
            &TrieValue::Account(test_account.clone()),
        );

        // child 1 is the root of page2
        slotted_page2.insert_value(&child_1).unwrap();
        let child_1_location = Location::from(slotted_page2.page_id());

        // child 2 is the root of page3
        slotted_page3.insert_value(&child_2).unwrap();
        let child_2_location = Location::from(slotted_page3.page_id());

        // next we create and update our root node
        let mut root_node = Node::new_branch(Nibbles::new());
        root_node.set_child(0, Pointer::new(child_1_location, RlpNode::default()));
        root_node.set_child(15, Pointer::new(child_2_location, RlpNode::default()));
        let root_node_page = storage_engine
            .get_mut_page(&context, context.metadata.root_subtrie_page_id)
            .unwrap();
        let mut slotted_page = SlottedPage::try_from(root_node_page).unwrap();
        let root_index = slotted_page.insert_value(&root_node).unwrap();
        assert_eq!(root_index, 0);

        // not necessary but let's commit our changes.
        storage_engine.commit(&context).unwrap();

        // assert we can get the children accounts we just added:
        let child_1_nibbles = Nibbles::from_nibbles(child_1_full_path);
        let child_2_nibbles = Nibbles::from_nibbles(child_2_full_path);
        let read_account1 = storage_engine
            .get_account(&context, AddressPath::new(child_1_nibbles.clone()))
            .unwrap();
        assert_eq!(read_account1, Some(test_account.clone()));
        let read_account2 = storage_engine
            .get_account(&context, AddressPath::new(child_2_nibbles.clone()))
            .unwrap();
        assert_eq!(read_account2, Some(test_account.clone()));

        // WHEN: child 1 is deleted
        storage_engine
            .set_accounts(
                &mut context,
                vec![(AddressPath::new(child_1_nibbles.clone()), None)],
            )
            .unwrap();

        // THEN: the root branch node should be deleted and the root node should be the leaf of child 2 on the child's page
        let root_node_page = storage_engine
            .get_page(&context, context.metadata.root_subtrie_page_id)
            .unwrap();
        let root_node_slotted = SlottedPage::try_from(root_node_page).unwrap();
        let root_node: Node = root_node_slotted.get_value(0).unwrap();
        assert!(!root_node.is_branch());
        assert_eq!(
            root_node_slotted.page_id(),
            child_2_location.page_id().unwrap()
        );

        // check that the prefix for root node has changed
        assert_eq!(root_node.prefix().clone(), child_2_nibbles);

        // test that we can get child 2 and not child 1
        let read_account2 = storage_engine
            .get_account(&context, AddressPath::new(child_2_nibbles))
            .unwrap();
        assert_eq!(read_account2, Some(test_account.clone()));
        let read_account1 = storage_engine
            .get_account(&context, AddressPath::new(child_1_nibbles))
            .unwrap();
        assert_eq!(read_account1, None);
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
        #![proptest_config(ProptestConfig::with_cases(100))]
        #[test]
        fn fuzz_insert_get_accounts(
            accounts in prop::collection::vec(
                (any::<Address>(), any::<Account>()),
                1..20
            )
        ) {
            let (storage_engine, mut context) = create_test_engine(10_000, 256);

            for (address, account) in &accounts {
                storage_engine
                    .set_accounts(&mut context, vec![(AddressPath::for_address(*address), Some(account.clone()))])
                    .unwrap();
            }

            for (address, account) in accounts {
                let read_account = storage_engine
                    .get_account(&context, AddressPath::for_address(address))
                    .unwrap();
                assert_eq!(read_account, Some(Account::new(account.nonce, account.balance, EMPTY_ROOT_HASH, account.code_hash)));
            }
        }
    }
}
