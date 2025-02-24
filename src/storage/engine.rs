use crate::{
    account::Account,
    database::Metadata,
    location::Location,
    node::Node,
    page::{
        OrphanPageManager, Page, PageError, PageId, PageManager, RootPage, SlottedPage, RO, RW,
    },
    path::AddressPath,
    pointer::Pointer,
    snapshot::SnapshotId,
};
use alloy_trie::{Nibbles, EMPTY_ROOT_HASH};
use log::{debug, trace};
use std::cmp::max;
use std::fmt::Debug;
use std::sync::Arc;
use std::sync::RwLock;

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

        if inner.isClosed() {
            return;
        }

        inner.orphan_manager.unlock(snapshot_id);
    }

    // Allocates a new page from the underlying page manager.
    // If there is an orphaned page available as of the given snapshot id,
    // it is used to allocate a new page instead.
    fn allocate_page<'p>(&self, metadata: &Metadata) -> Result<Page<'p, RW>, Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.isClosed() {
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

        if inner.isClosed() {
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

        if inner.isClosed() {
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

        if inner.isClosed() {
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
        trace!("get_account_from_page(): {:?} {:?}", path, page_index);

        let node: Node = slotted_page.get_value(page_index)?;
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
            let val: &[u8] = node.value().unwrap();
            return Ok(Some(A::from_bytes(val).unwrap()));
        }

        let child_pointer = node.child(remaining_path[0]);
        match child_pointer {
            Some(child_pointer) => {
                let child_location = child_pointer.location();
                if child_location.cell_index().is_some() {
                    self.get_account_from_page::<A>(
                        metadata,
                        remaining_path.slice(1..),
                        slotted_page,
                        child_location.cell_index().unwrap(),
                    )
                } else {
                    let child_page_id = child_location.page_id().unwrap();
                    let child_page = self.get_page(metadata, child_page_id)?;
                    let child_slotted_page = SlottedPage::try_from(child_page)?;
                    self.get_account_from_page::<A>(
                        metadata,
                        remaining_path.slice(1..),
                        child_slotted_page,
                        0,
                    )
                }
            }
            None => Ok(None),
        }
    }

    pub fn set_account<A: Account + Value + Clone>(
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
        let location = self.set_account_in_page(
            metadata,
            address_path.into(),
            account,
            root_subtrie_page_id,
            0,
        )?;
        metadata.root_subtrie_page_id = location.page_id().unwrap();
        Ok(())
    }

    fn set_account_in_page<A: Account + Value + Clone>(
        &self,
        metadata: &mut Metadata,
        path: Nibbles,
        account: A,
        page_id: PageId,
        page_index: u8,
    ) -> Result<Location, Error> {
        let page = self.get_mut_clone(metadata, page_id)?;
        let mut new_slotted_page = SlottedPage::try_from(page)?;
        let result = self.set_account_in_cloned_page(
            metadata,
            path.clone(),
            account.clone(),
            &mut new_slotted_page,
            page_index,
        );
        match result {
            Ok(location) => Ok(location),
            Err(Error::PageError(PageError::PageIsFull)) => {
                // Re-clone the page, split it, and try again. This orphans the first clone.
                // TODO: it's probably better if we can proactively split the page instead of needing this fallback behavior.
                // This would also allow us to avoid cloning the path and account.
                {
                    self.inner
                        .write()
                        .unwrap()
                        .orphan_manager
                        .add_orphaned_page_id(metadata.snapshot_id, new_slotted_page.page_id());
                }
                let page = self.get_mut_clone(metadata, page_id)?;
                let mut new_slotted_page = SlottedPage::try_from(page)?;
                self.split_page(metadata, &mut new_slotted_page)
                    .expect("split page should succeed");
                let location = self
                    .set_account_in_cloned_page(
                        metadata,
                        path,
                        account,
                        &mut new_slotted_page,
                        page_index,
                    )
                    .expect("set account in cloned page should succeed");
                Ok(location)
            }
            Err(e) => Err(e),
        }
    }

    fn set_account_in_cloned_page<A: Account + Value + Clone>(
        &self,
        metadata: &mut Metadata,
        path: Nibbles,
        account: A,
        slotted_page: &mut SlottedPage<'_, RW>,
        page_index: u8,
    ) -> Result<Location, Error> {
        let res = slotted_page.get_value::<Node>(page_index);
        if res.is_err() {
            // Trie is empty, insert the new account at the root.
            let new_node = Node::new_leaf(path, account.to_bytes().as_slice());
            let index = slotted_page.insert_value(new_node)?;
            assert_eq!(index, 0, "root node must be at index 0");
            return Ok(Location::for_page(slotted_page.page_id()));
        }

        let mut node = res.unwrap();
        let common_prefix_length = path.common_prefix_length(node.prefix());
        // find the common prefix between the path and the node prefix.
        let common_prefix = path.slice(0..common_prefix_length);
        if common_prefix_length < node.prefix().len() {
            // the path does not match the node prefix, so we need to create a new branch node as its parent.
            let mut new_parent_branch = Node::new_branch(common_prefix);
            let child_branch_index = path[common_prefix_length];
            let remaining_path = path.slice(common_prefix_length + 1..);
            let new_leaf_node = Node::new_leaf(remaining_path, account.to_bytes().as_slice());
            // update the prefix of the existing node and insert it into the page
            let node_branch_index = node.prefix()[common_prefix_length];
            node.set_prefix(node.prefix().slice(common_prefix_length + 1..));
            let location = Location::for_cell(slotted_page.insert_value(node)?);
            new_parent_branch.set_child(node_branch_index, Pointer::new_unhashed(location));
            let location = Location::for_cell(slotted_page.insert_value(new_leaf_node)?);
            new_parent_branch.set_child(child_branch_index, Pointer::new_unhashed(location));
            slotted_page.set_value(page_index, new_parent_branch)?;

            return Ok(self.node_location(slotted_page.page_id(), page_index));
        }

        if common_prefix_length == path.len() {
            // the path matches the node prefix exactly, so we can update the value.
            let new_node = Node::new_leaf(path, account.to_bytes().as_slice());
            slotted_page.set_value(page_index, new_node)?;

            return Ok(self.node_location(slotted_page.page_id(), page_index));
        }

        // the path is a prefix of the node prefix, so we need to traverse the node's children.
        let child_index = path[common_prefix_length];
        let remaining_path = path.slice(common_prefix_length + 1..);
        let child_pointer = node.child(child_index);
        match child_pointer {
            Some(child_pointer) => {
                // the child node exists, so we need to traverse it.
                let child_location = child_pointer.location();
                if let Some(child_cell_index) = child_location.cell_index() {
                    let location = self.set_account_in_cloned_page::<A>(
                        metadata,
                        remaining_path,
                        account,
                        slotted_page,
                        child_cell_index,
                    )?;
                    node.set_child(child_index, Pointer::new_unhashed(location));
                    slotted_page.set_value(page_index, node)?;

                    Ok(self.node_location(slotted_page.page_id(), page_index))
                } else {
                    let child_page_id = child_location.page_id().unwrap();
                    let location = self.set_account_in_page::<A>(
                        metadata,
                        remaining_path,
                        account,
                        child_page_id,
                        0,
                    )?;
                    node.set_child(child_index, Pointer::new_unhashed(location));
                    slotted_page.set_value(page_index, node)?;

                    Ok(self.node_location(slotted_page.page_id(), page_index))
                }
            }
            None => {
                // the child node does not exist, so we need to create a new leaf node with the remaining path.
                let new_node = Node::new_leaf(remaining_path, account.to_bytes().as_slice());
                let location = Location::for_cell(slotted_page.insert_value(new_node)?);
                node.set_child(child_index, Pointer::new_unhashed(location));
                slotted_page.set_value(page_index, node)?;

                Ok(self.node_location(slotted_page.page_id(), page_index))
            }
        }
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
        metadata: &mut Metadata,
        page: &mut SlottedPage<'_, RW>,
    ) -> Result<(), Error> {
        let child_page = self.allocate_page(metadata)?;
        let mut child_slotted_page = SlottedPage::try_from(child_page)?;

        let mut root_node: Node = page.get_value(0)?;

        // Find the child with the largest subtrie
        let (largest_child_index, largest_child_pointer) = root_node
            .enumerate_children()
            .max_by_key(|(_, ptr)| {
                // If pointer points to a cell in current page, count nodes in that subtrie
                if let Some(cell_index) = ptr.location().cell_index() {
                    self.count_subtrie_nodes(page, cell_index).unwrap_or(0)
                } else {
                    // If pointer points to another page, count as 0
                    0
                }
            })
            .ok_or(Error::PageError(PageError::PageIsFull))?;

        // Move the subtrie to the new page
        if let Some(cell_index) = largest_child_pointer.location().cell_index() {
            // Move all child nodes that are in the current page
            self.move_subtrie_nodes(page, cell_index, &mut child_slotted_page)?;

            // Update the pointer in the root node to point to the new page
            root_node.set_child(
                largest_child_index as u8,
                Pointer::new(
                    Location::for_page(child_slotted_page.page_id()),
                    largest_child_pointer.hash(),
                ),
            );
            page.set_value(0, root_node)?;
        }

        Ok(())
    }

    // Helper function to count nodes in a subtrie on the given page
    fn count_subtrie_nodes(&self, page: &SlottedPage<'_, RW>, root_index: u8) -> Result<u8, Error> {
        let mut count = 1; // Count the root node
        let node: Node = page.get_value(root_index)?;
        if !node.is_branch() {
            return Ok(count);
        }

        // Count child nodes that are in this page
        for (_, child_ptr) in node.enumerate_children() {
            if let Some(child_index) = child_ptr.location().cell_index() {
                count += self.count_subtrie_nodes(page, child_index)?;
            }
        }

        Ok(count)
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

        let is_branch = node.is_branch();

        // first insert the node into the new page to secure its location.
        let new_index = target_page.insert_value(node)?;

        // if the node has no children, we're done.
        if !is_branch {
            return Ok(Location::for_cell(new_index));
        }

        // otherwise, we need to move the children of the node.
        let mut updated_node: Node = target_page.get_value(new_index)?;

        // Process each child that's in the current page
        for branch_index in 0..16 {
            let child_ptr = updated_node.child(branch_index);
            if let Some(child_ptr) = child_ptr {
                if let Some(child_index) = child_ptr.location().cell_index() {
                    // Recursively move its children
                    let new_location =
                        self.move_subtrie_nodes(source_page, child_index, target_page)?;
                    // update the pointer in the parent node
                    updated_node.set_child(
                        branch_index as u8,
                        Pointer::new(new_location, child_ptr.hash()),
                    );
                }
            }
        }

        // update the parent node with the new child pointers.
        target_page.set_value(new_index, updated_node)?;

        Ok(self.node_location(target_page.page_id(), new_index))
    }

    // pub fn get_storage(&self, storage_path: StoragePath) -> Result<StorageValue, Error> {
    //     todo!()
    // }

    // pub fn set_storage(&mut self, storage_path: StoragePath, value: StorageValue) -> Result<(), Error> {
    //     todo!()
    // }

    pub fn commit(&self, metadata: &Metadata) -> Result<(), Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.isClosed() {
            return Err(Error::EngineClosed);
        }

        inner.commit(metadata)
    }

    pub fn rollback(&self, metadata: &Metadata) -> Result<(), Error> {
        todo!()
    }

    pub fn resize(&mut self, new_page_count: PageId) -> Result<(), Error> {
        let mut inner = self.inner.write().unwrap();

        if inner.isClosed() {
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

        if inner.isClosed() {
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
    fn isClosed(&self) -> bool {
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
        let state_root = EMPTY_ROOT_HASH;

        // First commit to ensure all changes are written before writing the new root page.
        self.page_manager.commit(metadata.snapshot_id)?;

        let page_mut = self
            .page_manager
            .get_mut(metadata.snapshot_id, metadata.root_page_id)
            .unwrap();
        // TODO: include the metadata in the new root page.
        let mut new_root_page = RootPage::new(page_mut, state_root);
        let orphaned_page_ids = self.orphan_manager.iter().map(|x| *x).collect();
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
}

impl From<PageError> for Error {
    fn from(error: PageError) -> Self {
        Error::PageError(error)
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::{address, hex, B256, U256};

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
        };
        let storage_engine = StorageEngine::new(manager, orphan_manager);
        (storage_engine, metadata)
    }

    fn create_test_account(balance: u64, nonce: u64) -> AccountVec {
        AccountVec::new(U256::from(balance), nonce, B256::ZERO, B256::ZERO)
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
            .split_page(&mut metadata, &mut slotted_page)
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
