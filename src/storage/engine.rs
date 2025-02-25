use crate::{
    account::{Account, AccountVec, TrieValue},
    database::Metadata,
    location::Location,
    node::{LeafType, Node},
    page::{
        OrphanPageManager, Page, PageError, PageId, PageManager, RootPage, SlottedPage,
        PAGE_DATA_SIZE, RO, RW,
    },
    path::{AddressPath, StoragePath},
    pointer::Pointer,
    snapshot::SnapshotId,
};
use alloy_primitives::B256;
use alloy_rlp::Encodable;
use alloy_trie::Nibbles;
use log::{debug, trace};
use std::cmp::max;
use std::fmt::Debug;
use std::sync::Arc;
use std::sync::RwLock;

use super::value::Value;
use alloy_primitives::StorageValue;

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
    fn allocate_page<'p>(&self, metadata: &Metadata) -> Result<Page<'p, RW>, Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        inner.allocate_page(metadata)
    }

    // Retrieves a mutable clone of a page from the underlying page manager.
    // The original page is marked as orphaned and a new page is allocated, potentially from an orphaned page.
    fn get_mut_clone<'p>(
        &self,
        metadata: &Metadata,
        page_id: PageId,
    ) -> Result<Page<'p, RW>, Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        let original_page = inner.page_manager.get_mut(metadata.snapshot_id, page_id)?;
        // if the page already has the correct snapshot id, return it without cloning.
        if original_page.snapshot_id() == metadata.snapshot_id {
            return Ok(original_page);
        }

        let mut new_page = inner.allocate_page(metadata)?;

        inner
            .orphan_manager
            .add_orphaned_page_id(metadata.snapshot_id, page_id);
        new_page
            .contents_mut()
            .copy_from_slice(original_page.contents());
        Ok(new_page)
    }

    fn get_page<'p>(&self, metadata: &Metadata, page_id: PageId) -> Result<Page<'p, RO>, Error> {
        let inner = self.inner.read().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        inner
            .page_manager
            .get(metadata.snapshot_id, page_id)
            .map_err(|e| e.into())
    }

    fn get_mut_page<'p>(
        &self,
        metadata: &Metadata,
        page_id: PageId,
    ) -> Result<Page<'p, RW>, Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        inner
            .page_manager
            .get_mut(metadata.snapshot_id, page_id)
            .map_err(|e| e.into())
    }

    pub fn get_account<A: Account + Value>(
        &self,
        metadata: &Metadata,
        address_path: AddressPath,
    ) -> Result<Option<A>, Error> {
        let page = self.get_page(metadata, metadata.root_subtrie_page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;

        debug!("get_account(): {:?}", address_path);

        self.get_account_from_page::<A>(metadata, address_path.into(), slotted_page, 0)
    }

    fn get_account_from_page<A: Account + Value>(
        &self,
        metadata: &Metadata,
        path: Nibbles,
        slotted_page: SlottedPage<'_, RO>,
        page_index: u8,
    ) -> Result<Option<A>, Error> {
        self.get_value_from_page::<A>(metadata, path, slotted_page, page_index)
    }

    fn get_value_from_page<V: Value>(
        &self,
        metadata: &Metadata,
        path: Nibbles,
        slotted_page: SlottedPage<'_, RO>,
        page_index: u8,
    ) -> Result<Option<V>, Error> {
        trace!("get_account_from_page(): {:?} {:?}", path, page_index);

        let node: Node<V> = slotted_page.get_value(page_index)?;
        trace!("node.prefix(): {:?}", node.prefix());

        let common_prefix_length = path.common_prefix_length(node.prefix());
        let common_prefix = path.slice(0..common_prefix_length);
        trace!("common_prefix: {:?}", common_prefix);
        if common_prefix_length < node.prefix().len() {
            return Ok(None);
        }

        let remaining_path = path.slice(common_prefix_length..);

        trace!("remaining_path: {:?}", remaining_path);
        if remaining_path.is_empty() {
            return Ok(Some(node.to_value()));
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
                    self.get_value_from_page::<V>(
                        metadata,
                        remaining_path,
                        slotted_page,
                        child_location.cell_index().unwrap(),
                    )
                } else {
                    let child_page_id = child_location.page_id().unwrap();
                    let child_page = self.get_page(metadata, child_page_id)?;
                    let child_slotted_page = SlottedPage::try_from(child_page)?;
                    self.get_value_from_page::<V>(metadata, remaining_path, child_slotted_page, 0)
                }
            }
            None => Ok(None),
        }
    }

    pub fn set_account<A: Account + Value + Encodable + Clone>(
        &self,
        metadata: &mut Metadata,
        address_path: AddressPath,
        account: Option<A>,
    ) -> Result<(), Error> {
        if account.is_none() {
            todo!("support deleting accounts");
        }

        let account = account.unwrap();
        trace!("set_account(): {:?}", address_path);

        let root_subtrie_page_id = metadata.root_subtrie_page_id;
        let pointer = self.set_value_in_page(
            metadata,
            address_path.into(),
            account,
            root_subtrie_page_id,
            0,
            LeafType::AccountLeaf,
        )?;
        metadata.root_subtrie_page_id = pointer.location().page_id().unwrap();
        metadata.state_root = pointer.rlp().as_hash().unwrap();
        Ok(())
    }

    fn set_value_in_page<V: Value + Encodable + Clone>(
        &self,
        metadata: &mut Metadata,
        path: Nibbles,
        value: V,
        page_id: PageId,
        page_index: u8,
        leaf_type: LeafType,
    ) -> Result<Pointer, Error> {
        let page = self.get_mut_clone(metadata, page_id)?;
        let mut new_slotted_page = SlottedPage::try_from(page)?;
        let result = self.set_value_in_cloned_page(
            metadata,
            path.clone(),
            value.clone(),
            &mut new_slotted_page,
            page_index,
            leaf_type,
        );
        match result {
            Ok(pointer) => Ok(pointer),
            // In the case of a page split, re-attempt the operation from scratch. This ensures that a page will be
            // consistently evaluated, and not modified in the middle of an operation, which could result in
            // inconsistent cell pointers.
            Err(Error::PageSplit) => self.set_value_in_cloned_page(
                metadata,
                path,
                value,
                &mut new_slotted_page,
                page_index,
                leaf_type,
            ),
            Err(Error::PageError(PageError::PageIsFull)) => {
                panic!("Page is full!");
            }
            Err(e) => Err(e),
        }
    }

    fn set_value_in_cloned_page<V: Value + Encodable + Clone>(
        &self,
        metadata: &mut Metadata,
        path: Nibbles,
        value: V,
        slotted_page: &mut SlottedPage<'_, RW>,
        page_index: u8,
        leaf_type: LeafType,
    ) -> Result<Pointer, Error> {
        let res = slotted_page.get_value::<Node<V>>(page_index);
        if res.is_err() {
            // Trie is empty, insert the new account at the root.
            let new_node = Node::new_leaf(path, value, leaf_type);
            let rlp_node = new_node.rlp_encode();
            let index = slotted_page.insert_value(new_node)?;
            assert_eq!(index, 0, "root node must be at index 0");
            return Ok(Pointer::new(
                Location::for_page(slotted_page.page_id()),
                rlp_node,
            ));
        }

        let mut node = res.unwrap();
        let common_prefix_length = path.common_prefix_length(node.prefix());
        // find the common prefix between the path and the node prefix.
        let common_prefix = path.slice(0..common_prefix_length);
        if common_prefix_length < node.prefix().len() {
            // the path does not match the node prefix, so we need to create a new branch node as its parent.
            // ensure that the page has enough space (1100 bytes) to insert a new branch and leaf node.
            // TODO: use a more accurate threshold
            if slotted_page.num_free_bytes() < 1100 {
                self.split_page::<V>(metadata, slotted_page)?;
                return Err(Error::PageSplit);
            }
            let mut new_parent_branch: Node<V> = Node::new_branch(common_prefix);
            let child_branch_index = path[common_prefix_length];
            let remaining_path = path.slice(common_prefix_length + 1..);
            let new_leaf_node = Node::new_leaf(remaining_path, value, leaf_type);
            // update the prefix of the existing node and insert it into the page
            let node_branch_index = node.prefix()[common_prefix_length];
            node.set_prefix(node.prefix().slice(common_prefix_length + 1..));
            let rlp_node = node.rlp_encode();
            let location = Location::for_cell(slotted_page.insert_value(node)?);
            new_parent_branch.set_child(node_branch_index, Pointer::new(location, rlp_node));
            let rlp_node = new_leaf_node.rlp_encode();
            let location = Location::for_cell(slotted_page.insert_value(new_leaf_node)?);
            new_parent_branch.set_child(child_branch_index, Pointer::new(location, rlp_node));
            let rlp_branch_node = new_parent_branch.rlp_encode();
            slotted_page.set_value(page_index, new_parent_branch)?;

            return Ok(Pointer::new(
                self.node_location(slotted_page.page_id(), page_index),
                rlp_branch_node,
            ));
        }

        if common_prefix_length == path.len() {
            // the path matches the node prefix exactly, so we can update the value.
            let new_node = Node::new_leaf(path, value, leaf_type);
            let rlp_node = new_node.rlp_encode();
            slotted_page.set_value(page_index, new_node)?;

            return Ok(Pointer::new(
                self.node_location(slotted_page.page_id(), page_index),
                rlp_node,
            ));
        }

        // the path is a prefix of the node prefix, so we need to traverse the node's children.
        let child_index = path[common_prefix_length];

        let remaining_path = if !node.is_branch() {
            // if we are at an AccountLeaf, we need a "free hop" to the storage trie
            // so the remaining_path needs to contain the current nibble.
            path.slice(common_prefix_length..)
        } else {
            path.slice(common_prefix_length + 1..)
        };

        // Note: if the node is an AccountLeaf, there is no such thing as a "child_index"
        // so node.child(...) will always return the storage_root.
        let child_pointer = if !node.is_branch() {
            node.direct_child()
        } else {
            node.child(child_index)
        };

        match child_pointer {
            Some(child_pointer) => {
                // the child node exists, so we need to traverse it.
                let child_location = child_pointer.location();
                if let Some(child_cell_index) = child_location.cell_index() {
                    let child_pointer = self.set_value_in_cloned_page::<V>(
                        metadata,
                        remaining_path,
                        value,
                        slotted_page,
                        child_cell_index,
                        leaf_type,
                    )?;
                    node.set_child(child_index, child_pointer.clone());
                    if !node.is_branch() {
                        // We are at an AccountLeaf and our storage just changed. Let's update our storage root.
                        return self.update_account_storage_root(
                            node,
                            child_pointer.rlp().as_hash().unwrap(),
                            slotted_page,
                            page_index,
                        );
                    }
                    let rlp_node = node.rlp_encode();
                    slotted_page.set_value(page_index, node)?;

                    Ok(Pointer::new(
                        self.node_location(slotted_page.page_id(), page_index),
                        rlp_node,
                    ))
                } else {
                    // otherwise, insert the new account into the empty child slot.
                    let child_page_id = child_location.page_id().unwrap();
                    let child_pointer = self.set_value_in_page::<V>(
                        metadata,
                        remaining_path,
                        value,
                        child_page_id,
                        0,
                        leaf_type,
                    )?;
                    node.set_child(child_index, child_pointer.clone());
                    if !node.is_branch() {
                        // We are at an AccountLeaf and our storage just changed. Let's update our storage root.
                        return self.update_account_storage_root(
                            node,
                            child_pointer.rlp().as_hash().unwrap(),
                            slotted_page,
                            page_index,
                        );
                    }
                    let rlp_node = node.rlp_encode();
                    slotted_page.set_value(page_index, node)?;

                    Ok(Pointer::new(
                        self.node_location(slotted_page.page_id(), page_index),
                        rlp_node,
                    ))
                }
            }
            None => {
                // the child node does not exist, so we need to create a new leaf node with the remaining path.
                // ensure that the page has enough space (300 bytes) to insert a new leaf node.
                // TODO: use a more accurate threshold
                if slotted_page.num_free_bytes() < 300 {
                    self.split_page::<V>(metadata, slotted_page)?;
                    return Err(Error::PageSplit);
                }
                let new_node = Node::new_leaf(remaining_path, value, leaf_type);
                let rlp_node = new_node.rlp_encode();
                let location = Location::for_cell(slotted_page.insert_value(new_node)?);
                node.set_child(child_index, Pointer::new(location, rlp_node.clone()));
                if !node.is_branch() {
                    // We are at an AccountLeaf and our storage just changed. Let's update our storage root.
                    return self.update_account_storage_root(
                        node,
                        rlp_node.as_hash().unwrap(),
                        slotted_page,
                        page_index,
                    );
                }

                let rlp_node_with_child = node.rlp_encode();
                slotted_page.set_value(page_index, node)?;
                Ok(Pointer::new(
                    self.node_location(slotted_page.page_id(), page_index),
                    rlp_node_with_child,
                ))
            }
        }
    }

    fn update_account_storage_root<V: Value>(
        &self,
        node: Node<V>,
        new_storage_root: B256,
        slotted_page: &mut SlottedPage<'_, RW>,
        page_index: u8,
    ) -> Result<Pointer, Error> {
        // We are at an AccountLeaf and our storage just changed. Let's update our storage root.
        let value = node.value().expect("must be account leaf");
        let account: AccountVec = AccountVec::from_bytes(value.to_bytes().as_slice())
            .expect("valid account vector encoding");
        let updated_account = AccountVec::new(
            account.balance(),
            account.nonce(),
            account.code_hash(),
            new_storage_root,
        );
        let new_account_leaf: Node<AccountVec> = Node::new_account_leaf(
            node.prefix().clone(),
            updated_account,
            node.direct_child().cloned(),
        );

        let rlp_node_with_child = new_account_leaf.rlp_encode();
        slotted_page.set_value(page_index, new_account_leaf)?;

        Ok(Pointer::new(
            self.node_location(slotted_page.page_id(), page_index),
            rlp_node_with_child,
        ))
    }

    fn node_location(&self, page_id: PageId, page_index: u8) -> Location {
        if page_index == 0 {
            Location::for_page(page_id)
        } else {
            Location::for_cell(page_index)
        }
    }

    // Split the page into two, moving the largest immediate subtrie of the root node to a new child page.
    fn split_page<V: Value>(
        &self,
        metadata: &mut Metadata,
        page: &mut SlottedPage<'_, RW>,
    ) -> Result<(), Error> {
        while page.num_free_bytes() < PAGE_DATA_SIZE / 3 as usize {
            let child_page = self.allocate_page(metadata)?;
            let mut child_slotted_page = SlottedPage::try_from(child_page)?;

            let mut root_node: Node<V> = page.get_value(0)?;

            // Find the child with the largest subtrie
            let (largest_child_index, largest_child_pointer) = root_node
                .enumerate_children()
                .into_iter()
                .max_by_key(|(_, ptr)| {
                    // If pointer points to a cell in current page, count nodes in that subtrie
                    if let Some(cell_index) = ptr.location().cell_index() {
                        self.count_subtrie_nodes::<V>(page, cell_index).unwrap_or(0)
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
                    self.move_subtrie_nodes::<V>(page, cell_index, &mut child_slotted_page)?;
                assert!(
                    location.page_id().is_some(),
                    "expected subtrie to be moved to a new page"
                );

                // Update the pointer in the root node to point to the new page
                root_node.set_child(
                    largest_child_index as u8,
                    Pointer::new(location, largest_child_pointer.rlp().clone()),
                );
                page.set_value(0, root_node)?;
            }
        }

        Ok(())
    }

    // Helper function to count nodes in a subtrie on the given page
    fn count_subtrie_nodes<V: Value>(
        &self,
        page: &SlottedPage<'_, RW>,
        root_index: u8,
    ) -> Result<u8, Error> {
        let mut count = 1; // Count the root node
        let node: Node<V> = page.get_value(root_index)?;
        if !node.has_children() {
            return Ok(count);
        }

        // Count child nodes that are in this page
        for (_, child_ptr) in node.enumerate_children() {
            if let Some(child_index) = child_ptr.location().cell_index() {
                count += self.count_subtrie_nodes::<V>(page, child_index)?;
            }
        }

        Ok(count)
    }

    // Helper function to move an entire subtrie from one page to another.
    fn move_subtrie_nodes<V: Value>(
        &self,
        source_page: &mut SlottedPage<'_, RW>,
        root_index: u8,
        target_page: &mut SlottedPage<'_, RW>,
    ) -> Result<Location, Error> {
        let node: Node<V> = source_page.get_value(root_index)?;
        source_page.delete_value(root_index)?;

        let has_children = node.has_children();

        // first insert the node into the new page to secure its location.
        let new_index = target_page.insert_value(node)?;

        // if the node has no children, we're done.
        if !has_children {
            return Ok(self.node_location(target_page.page_id(), new_index));
        }

        // otherwise, we need to move the children of the node.
        let mut updated_node: Node<V> = target_page.get_value(new_index)?;

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
                        self.move_subtrie_nodes::<V>(source_page, child_index, target_page)?;
                    // update the pointer in the parent node
                    updated_node.set_child(
                        branch_index as u8,
                        Pointer::new(new_location, child_ptr.rlp().clone()),
                    );
                }
            }
        }

        // update the parent node with the new child pointers.
        target_page.set_value(new_index, updated_node)?;

        Ok(self.node_location(target_page.page_id(), new_index))
    }

    pub fn get_storage(
        &self,
        metadata: &Metadata,
        storage_path: StoragePath,
    ) -> Result<Option<StorageValue>, Error> {
        let page = self.get_page(metadata, metadata.root_subtrie_page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;

        match self.get_value_from_page::<TrieValue>(
            metadata,
            storage_path.full_path(),
            slotted_page,
            0,
        )? {
            Some(TrieValue::Storage(storage_value)) => Ok(Some(storage_value)),
            _ => Ok(None),
        }
    }

    pub fn set_storage(
        &mut self,
        metadata: &mut Metadata,
        storage_path: StoragePath,
        value: StorageValue,
    ) -> Result<(), Error> {
        let trie_value = TrieValue::Storage(value);
        let pointer = self.set_value_in_page::<TrieValue>(
            metadata,
            storage_path.full_path(),
            trie_value,
            metadata.root_subtrie_page_id,
            0,
            LeafType::StorageLeaf,
        )?;

        metadata.root_subtrie_page_id = pointer.location().page_id().unwrap();
        metadata.state_root = pointer.rlp().as_hash().unwrap();

        Ok(())
    }

    pub fn commit(&self, metadata: &Metadata) -> Result<(), Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        inner.commit(metadata)
    }

    pub fn rollback(&self, metadata: &Metadata) -> Result<(), Error> {
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

    pub fn close(&self, metadata: &Metadata) -> Result<(), Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.is_closed() {
            return Err(Error::EngineClosed);
        }

        let underlying_root_page = inner
            .page_manager
            .get(metadata.snapshot_id, metadata.root_page_id)?;
        let root_page = RootPage::try_from(underlying_root_page).map_err(Error::PageError)?;

        // there will always be a minimum of 2 root pages
        let max_page_count = max(root_page.max_page_number(), 2);
        // resize the page manager so that we only store the exact amount of pages we need.
        inner.resize(max_page_count)?;
        // commit all outstanding data to disk.
        inner.commit(metadata)?;
        // mark engine as closed, causing all operations on engine to return an error.
        inner.status = Status::Closed;

        Ok(())
    }
}

impl<P: PageManager> Inner<P> {
    fn is_closed(&self) -> bool {
        match self.status {
            Status::Closed => true,
            _ => false,
        }
    }

    fn allocate_page<'p>(&mut self, metadata: &Metadata) -> Result<Page<'p, RW>, Error> {
        let snapshot_id = metadata.snapshot_id;
        let orphaned_page_id = self.orphan_manager.get_orphaned_page_id();
        if let Some(orphaned_page_id) = orphaned_page_id {
            let mut page = self.page_manager.get_mut(snapshot_id, orphaned_page_id)?;
            page.set_snapshot_id(snapshot_id);
            page.contents_mut().fill(0);
            Ok(page)
        } else {
            self.page_manager
                .allocate(snapshot_id)
                .map_err(|e| e.into())
        }
    }

    fn resize(&mut self, new_page_count: PageId) -> Result<(), Error> {
        self.page_manager.resize(new_page_count)?;
        Ok(())
    }

    fn commit(&mut self, metadata: &Metadata) -> Result<(), Error> {
        // First commit to ensure all changes are written before writing the new root page.
        self.page_manager.commit(metadata.snapshot_id)?;

        let page_mut = self
            .page_manager
            .get_mut(metadata.snapshot_id, metadata.root_page_id)
            .unwrap();
        // TODO: include the remaining metadata in the new root page.
        let mut new_root_page = RootPage::new(page_mut, metadata.state_root);
        let orphaned_page_ids = self.orphan_manager.iter().copied().collect();
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
        self.page_manager.commit(metadata.snapshot_id)?;

        Ok(())
    }
}

#[derive(Debug)]
pub enum Error {
    PageError(PageError),
    InvalidPath,
    InvalidSnapshotId,
    EngineClosed,
    PageSplit,
}

impl From<PageError> for Error {
    fn from(error: PageError) -> Self {
        Error::PageError(error)
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::{address, b256, hex, keccak256, Address, StorageKey, U256};
    use alloy_rlp::encode;
    use alloy_trie::{
        root::{storage_root_unhashed, storage_root_unsorted},
        EMPTY_ROOT_HASH, KECCAK_EMPTY,
    };

    use super::*;
    use crate::{account::AccountVec, page::MmapPageManager};

    fn create_test_engine(
        page_count: u32,
        root_subtrie_page_id: PageId,
    ) -> (StorageEngine<MmapPageManager>, Metadata) {
        let manager = MmapPageManager::new_anon(page_count, root_subtrie_page_id + 1).unwrap();
        let orphan_manager = OrphanPageManager::new();
        let metadata = Metadata {
            snapshot_id: 1,
            root_page_id: 0,
            root_subtrie_page_id,
            state_root: EMPTY_ROOT_HASH,
        };
        let storage_engine = StorageEngine::new(manager, orphan_manager);
        (storage_engine, metadata)
    }

    fn create_test_account(balance: u64, nonce: u64) -> AccountVec {
        AccountVec::new(U256::from(balance), nonce, KECCAK_EMPTY, EMPTY_ROOT_HASH)
    }

    #[test]
    fn test_allocate_get_mut_clone() {
        let (storage_engine, mut metadata) = create_test_engine(10, 1);

        // Initial allocation
        let mut page = storage_engine.allocate_page(&metadata).unwrap();
        assert_eq!(page.page_id(), 2);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 1);

        // mutation
        page.contents_mut()[0] = 123;
        storage_engine.commit(&metadata).unwrap();
        metadata = metadata.next();

        // reading mutated page
        let page = storage_engine.get_page(&metadata, 2).unwrap();
        assert_eq!(page.page_id(), 2);
        assert_eq!(page.contents()[0], 123);
        assert_eq!(page.snapshot_id(), 1);

        // cloning a page should allocate a new page and orphan the original page
        let cloned_page = storage_engine.get_mut_clone(&metadata, 2).unwrap();
        assert_eq!(cloned_page.page_id(), 3);
        assert_eq!(cloned_page.contents()[0], 123);
        assert_eq!(cloned_page.snapshot_id(), 2);
        assert_ne!(cloned_page.page_id(), page.page_id());

        // the next allocation should not come from the orphaned page, as the snapshot id is the same as when the page was orphaned
        let page = storage_engine.allocate_page(&metadata).unwrap();
        assert_eq!(page.page_id(), 4);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 2);

        storage_engine.commit(&metadata).unwrap();
        metadata = metadata.next();

        // the next allocation should not come from the orphaned page, as the snapshot has not been unlocked yet
        let page = storage_engine.allocate_page(&metadata).unwrap();
        assert_eq!(page.page_id(), 5);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 3);

        storage_engine.unlock(3);

        // the next allocation should come from the orphaned page because the snapshot id has increased.
        // The page data should be zeroed out.
        let page = storage_engine.allocate_page(&metadata).unwrap();
        assert_eq!(page.page_id(), 2);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 3);
    }

    #[test]
    fn test_shared_page_mutability() {
        let (storage_engine, metadata) = create_test_engine(10, 1);

        let page1 = storage_engine.get_page(&metadata, 1).unwrap();
        assert_eq!(page1.contents()[0], 0);

        let mut page2 = storage_engine.get_mut_page(&metadata, 1).unwrap();
        page2.contents_mut()[0] = 123;

        storage_engine.commit(&metadata).unwrap();

        assert_eq!(page1.contents()[0], 123);
        assert_eq!(page2.contents()[0], 123);
    }

    #[test]
    fn test_set_get_account() {
        let (storage_engine, mut metadata) = create_test_engine(300, 256);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_account(
                &mut metadata,
                AddressPath::for_address(address),
                Some(account.clone()),
            )
            .unwrap();
        assert_eq!(metadata.root_subtrie_page_id, 257);

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

            let read_account = storage_engine
                .get_account::<AccountVec>(&metadata, path.clone())
                .unwrap();
            assert_eq!(read_account, None);

            storage_engine
                .set_account(&mut metadata, path, Some(account.clone()))
                .unwrap();
        }

        // Verify all accounts exist after insertion
        for (address, account) in &test_cases {
            let read_account = storage_engine
                .get_account::<AccountVec>(&metadata, AddressPath::for_address(*address))
                .unwrap();
            assert_eq!(read_account, Some(account.clone()));
        }
    }

    #[test]
    fn test_simple_trie_state_root_1() {
        let (storage_engine, mut metadata) = create_test_engine(300, 256);

        let address1 = address!("0x8e64566b5eb8f595f7eb2b8d302f2e5613cb8bae");
        let account1 = create_test_account(1_000_000_000_000_000_000u64, 0);
        let path1 = AddressPath::for_address(address1);

        let address2 = address!("0xcea8f2236efa20c8fadeb9d66e398a6532cca6c8");
        let account2 = create_test_account(14_000_000_000_000_000_000u64, 1);
        let path2 = AddressPath::for_address(address2);

        storage_engine
            .set_account(&mut metadata, path1, Some(account1.clone()))
            .unwrap();
        storage_engine
            .set_account(&mut metadata, path2, Some(account2.clone()))
            .unwrap();

        assert_eq!(
            metadata.state_root,
            b256!("0x0d9348243d7357c491e6a61f4b1305e77dc6acacdb8cc708e662f6a9bab6ca02")
        );
    }

    #[test]
    fn test_simple_trie_state_root_2() {
        let (storage_engine, mut metadata) = create_test_engine(300, 256);

        let address1 = address!("0x000f3df6d732807ef1319fb7b8bb8522d0beac02");
        let account1 = AccountVec::new(U256::from(0), 1, keccak256(hex!("0x3373fffffffffffffffffffffffffffffffffffffffe14604d57602036146024575f5ffd5b5f35801560495762001fff810690815414603c575f5ffd5b62001fff01545f5260205ff35b5f5ffd5b62001fff42064281555f359062001fff015500")), EMPTY_ROOT_HASH);
        let path1 = AddressPath::for_address(address1);

        let address2 = address!("0x0000000000000000000000000000000000001000");
        let account2 = AccountVec::new(U256::from(0x010000000000u64), 1, keccak256(hex!("0x366000602037602060003660206000720f3df6d732807ef1319fb7b8bb8522d0beac02620186a0f16000556000516001553d6002553d600060003e600051600355")), EMPTY_ROOT_HASH);
        let path2 = AddressPath::for_address(address2);

        let address3 = address!("0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b");
        let account3 = AccountVec::new(
            U256::from(0x3635c9adc5dea00000u128),
            0,
            KECCAK_EMPTY,
            EMPTY_ROOT_HASH,
        );
        let path3 = AddressPath::for_address(address3);

        storage_engine
            .set_account(&mut metadata, path1, Some(account1.clone()))
            .unwrap();
        storage_engine
            .set_account(&mut metadata, path2, Some(account2.clone()))
            .unwrap();
        storage_engine
            .set_account(&mut metadata, path3, Some(account3.clone()))
            .unwrap();

        assert_eq!(
            metadata.state_root,
            b256!("0x6f78ee01791dd8a62b4e2e86fae3d7957df9fa7f7a717ae537f90bb0c79df296")
        );
    }

    #[test]
    fn test_set_get_account_common_prefix() {
        let (storage_engine, mut metadata) = create_test_engine(300, 256);

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
                .set_account(&mut metadata, path, Some(account.clone()))
                .unwrap();
        }

        // Verify all accounts exist
        for (nibbles, account) in test_accounts {
            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let read_account = storage_engine
                .get_account::<AccountVec>(&metadata, path)
                .unwrap();
            assert_eq!(read_account, Some(account));
        }
    }

    #[test]
    fn test_split_page() {
        let (storage_engine, mut metadata) = create_test_engine(300, 256);

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
                .set_account(&mut metadata, path, Some(account.clone()))
                .unwrap();
        }

        // Split the page
        let page = storage_engine.get_mut_page(&metadata, 257).unwrap();
        let mut slotted_page = SlottedPage::try_from(page).unwrap();
        storage_engine
            .split_page::<AccountVec>(&mut metadata, &mut slotted_page)
            .unwrap();

        // Verify all accounts still exist after split
        for (nibbles, account) in test_accounts {
            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let read_account = storage_engine
                .get_account::<AccountVec>(&metadata, path)
                .unwrap();
            assert_eq!(read_account, Some(account));
        }
    }

    #[test]
    fn test_insert_get_1000_accounts() {
        let (storage_engine, mut metadata) = create_test_engine(5000, 256);

        for i in 0..1000 {
            let path = address_path_for_idx(i);
            let account = create_test_account(i, i);
            storage_engine
                .set_account(&mut metadata, path.clone(), Some(account.clone()))
                .unwrap();

            metadata.snapshot_id += 1;
        }

        for i in 0..1000 {
            let path = address_path_for_idx(i);
            let account = storage_engine
                .get_account::<AccountVec>(&metadata, path.clone())
                .unwrap();
            assert_eq!(account, Some(create_test_account(i, i)));
        }
    }

    #[test]
    #[should_panic]
    fn test_set_storage_slot_with_no_account_panics() {
        let (mut storage_engine, mut metadata) = create_test_engine(300, 256);
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");

        let storage_key =
            b256!("0x0000000000000000000000000000000000000000000000000000000000000000");
        let storage_value =
            b256!("0x0000000000000000000000000000000000000000000000000000000062617365");

        let storage_path = StoragePath::for_address_and_slot(address.clone(), storage_key);

        let storage_value = StorageValue::from_be_slice(&storage_value.as_slice());

        storage_engine
            .set_storage(&mut metadata, storage_path, storage_value)
            .unwrap();
    }

    #[test]
    fn test_set_get_account_storage_slots() {
        let (mut storage_engine, mut metadata) = create_test_engine(300, 256);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_account(
                &mut metadata,
                AddressPath::for_address(address),
                Some(account.clone()),
            )
            .unwrap();
        assert_eq!(metadata.root_subtrie_page_id, 257);

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
        for (storage_key, storage_value) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address.clone(), *storage_key);

            let read_storage_slot = storage_engine
                .get_storage(&metadata, storage_path.clone())
                .unwrap();
            assert_eq!(read_storage_slot, None);

            let storage_value = StorageValue::from_be_slice(&storage_value.as_slice());

            storage_engine
                .set_storage(&mut metadata, storage_path, storage_value)
                .unwrap();

            metadata = metadata.next();
        }

        // Verify all storage slots exist after insertion
        for (storage_key, storage_value) in &test_cases {
            let storage_path = StoragePath::for_address_and_slot(address.clone(), *storage_key);
            let read_storage_slot = storage_engine.get_storage(&metadata, storage_path).unwrap();
            let storage_value = StorageValue::from_be_slice(&storage_value.as_slice());
            assert_eq!(read_storage_slot, Some(storage_value));
        }
    }

    #[test]
    fn test_set_get_account_storage_roots() {
        let (mut storage_engine, mut metadata) = create_test_engine(300, 256);

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account = create_test_account(100, 1);
        storage_engine
            .set_account(
                &mut metadata,
                AddressPath::for_address(address),
                Some(account.clone()),
            )
            .unwrap();
        assert_eq!(metadata.root_subtrie_page_id, 257);

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
            let storage_path = StoragePath::for_address_and_slot(address.clone(), *storage_key);

            let read_storage_slot = storage_engine
                .get_storage(&metadata, storage_path.clone())
                .unwrap();
            assert_eq!(read_storage_slot, None);

            let storage_value = StorageValue::from_be_slice(&storage_value.as_slice());

            storage_engine
                .set_storage(&mut metadata, storage_path, storage_value)
                .unwrap();

            metadata = metadata.next();
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
            .get_account::<AccountVec>(&metadata, AddressPath::for_address(address))
            .unwrap()
            .unwrap();

        let storage_root = account.storage_root();
        assert_eq!(storage_root, expected_root);
    }

    #[test]
    fn test_set_get_many_accounts_storage_roots() {
        let (mut storage_engine, mut metadata) = create_test_engine(2000, 256);

        for i in 0..100 {
            let address =
                Address::from_slice(&keccak256((i as u32).to_le_bytes()).as_slice()[0..20]);
            let path = AddressPath::for_address(address);
            let account = create_test_account(i, i);
            storage_engine
                .set_account(&mut metadata, path.clone(), Some(account.clone()))
                .unwrap();

            metadata.snapshot_id += 1;
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
                    .set_storage(&mut metadata, storage_path.clone(), storage_slot_value)
                    .unwrap();

                keys_values.push((
                    B256::from_slice(storage_path.get_slot().pack().as_slice()),
                    storage_slot_value,
                ))
            }

            let expected_root = storage_root_unsorted(keys_values.into_iter());

            // check the storage root of the account
            let account = storage_engine
                .get_account::<AccountVec>(&metadata, path)
                .unwrap()
                .unwrap();

            let storage_root = account.storage_root();
            assert_eq!(storage_root, expected_root);
        }
    }

    fn test_split_page_stress() {
        // Create a storage engine with limited pages to force splits
        let (storage_engine, mut metadata) = create_test_engine(2000, 256);

        // Create a large number of accounts with different patterns to stress the trie

        // Pattern 1: Accounts with common prefixes to create deep branches
        let mut accounts = Vec::new();
        for i in 0..4096 {
            // Create paths with common prefixes but different endings
            let mut nibbles = [0u8; 64];
            // First 32 nibbles are the same
            for j in 0..32 {
                nibbles[j] = (j % 16) as u8;
            }
            // Last 30 nibbles vary
            for j in 32..64 {
                nibbles[j] = ((i + j) % 16) as u8;
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
            for j in 3..64 {
                nibbles[j] = ((i * j) % 16) as u8;
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
                for j in 1..62 {
                    nibbles[j] = ((i + j) % 16) as u8;
                }
            } else {
                nibbles[0] = 11; // Different arbitrary value
                for j in 1..62 {
                    nibbles[j] = ((i + j) % 16) as u8;
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
                .set_account(&mut metadata, path.clone(), Some(account.clone()))
                .unwrap();
        }

        // Verify all accounts exist with correct values
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine
                .get_account::<AccountVec>(&metadata, path.clone())
                .unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "Account mismatch for path: {:?}",
                path
            );
        }

        // Force multiple splits to stress the system
        // Find all pages in the trie and split them recursively
        let mut pages_to_split = vec![metadata.root_subtrie_page_id];
        while let Some(page_id) = pages_to_split.pop() {
            let page_result = storage_engine.get_mut_page(&metadata, page_id);
            if matches!(
                page_result,
                Err(Error::PageError(PageError::PageNotFound(_)))
            ) {
                break;
            }
            let mut slotted_page = SlottedPage::try_from(page_result.unwrap()).unwrap();

            // Try to split this page
            if let Ok(_) = storage_engine.split_page::<AccountVec>(&mut metadata, &mut slotted_page)
            {
                // If split succeeded, add the new pages to be processed
                pages_to_split.push(page_id + 1); // New page created by split
            }
        }

        // Verify all accounts still exist with correct values after splits
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine
                .get_account::<AccountVec>(&metadata, path.clone())
                .unwrap();
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
            for j in 1..62 {
                nibbles[j] = ((i * j + 7) % 16) as u8; // Different pattern
            }

            nibbles[62] = (i % 16) as u8;
            nibbles[63] = ((i / 16) % 16) as u8;

            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let account = create_test_account(i as u64 * 5000, i as u64 * 5);
            additional_accounts.push((path, account));
        }

        // Insert additional accounts
        for (path, account) in &additional_accounts {
            storage_engine
                .set_account(&mut metadata, path.clone(), Some(account.clone()))
                .unwrap();
        }

        // Verify all original accounts still exist
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine
                .get_account::<AccountVec>(&metadata, path.clone())
                .unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "Original account lost after adding new accounts"
            );
        }

        // Verify all new accounts exist
        for (path, expected_account) in &additional_accounts {
            let retrieved_account = storage_engine
                .get_account::<AccountVec>(&metadata, path.clone())
                .unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "New account not found"
            );
        }
    }

    #[test]
    fn test_split_page_random_accounts() {
        use rand::rngs::StdRng;
        use rand::{Rng, SeedableRng};

        // Create a storage engine
        let (storage_engine, mut metadata) = create_test_engine(2000, 256);

        // Use a seeded RNG for reproducibility
        let mut rng = StdRng::seed_from_u64(42);

        // Generate a large number of random accounts
        let mut accounts = Vec::new();
        for i in 0..3000 {
            let mut nibbles = [0u8; 64];
            // Generate random nibbles
            for j in 0..64 {
                nibbles[j] = rng.random_range(0..16) as u8;
            }

            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            let balance = rng.random_range(0..1_000_000);
            let nonce = rng.random_range(0..100);
            let account = create_test_account(balance, nonce);
            accounts.push((path, account));
        }

        // Insert all accounts
        for (path, account) in &accounts {
            storage_engine
                .set_account(&mut metadata, path.clone(), Some(account.clone()))
                .unwrap();
        }

        // Verify all accounts exist with correct values
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine
                .get_account::<AccountVec>(&metadata, path.clone())
                .unwrap();
            assert_eq!(retrieved_account, Some(expected_account.clone()));
        }

        // Get all pages and force splits on them
        let mut page_ids = Vec::new();
        // Start with the root page
        page_ids.push(metadata.root_subtrie_page_id);

        // Process each page
        for i in 0..page_ids.len() {
            let page_id = page_ids[i];

            // Try to get and split the page
            if let Ok(page) = storage_engine.get_mut_page(&metadata, page_id) {
                if let Ok(mut slotted_page) = SlottedPage::try_from(page) {
                    // Force a split
                    let _ =
                        storage_engine.split_page::<AccountVec>(&mut metadata, &mut slotted_page);

                    // Get the node to find child pages
                    if let Ok(node) = slotted_page.get_value::<Node<AccountVec>>(0) {
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
            let retrieved_account = storage_engine
                .get_account::<AccountVec>(&metadata, path.clone())
                .unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "Account mismatch after splitting multiple pages"
            );
        }

        // Create a vector to store updates
        let mut updates = Vec::new();

        // Prepare updates for some existing accounts
        for i in 0..accounts.len() {
            if i % 5 == 0 {
                // Update every 5th account
                let (path, _) = &accounts[i];
                let new_balance = rng.random_range(0..1_000_000);
                let new_nonce = rng.random_range(0..100);
                let new_account = create_test_account(new_balance, new_nonce);

                updates.push((i, path.clone(), new_account));
            }
        }

        // Apply the updates to both the trie and our test data
        for (idx, path, new_account) in &updates {
            // Update in the trie
            storage_engine
                .set_account(&mut metadata, path.clone(), Some(new_account.clone()))
                .unwrap();

            // Update in our test data
            accounts[*idx] = (path.clone(), new_account.clone());
        }

        // Verify all accounts have correct values after updates
        for (path, expected_account) in &accounts {
            let retrieved_account = storage_engine
                .get_account::<AccountVec>(&metadata, path.clone())
                .unwrap();
            assert_eq!(
                retrieved_account,
                Some(expected_account.clone()),
                "Account mismatch after updates"
            );
        }
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
}
