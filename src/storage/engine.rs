use crate::{
    account::Account,
    database::Metadata,
    node::Node,
    page::{
        OrphanPageManager, Page, PageError, PageId, PageManager, RootPage, SlottedPage, RO, RW,
    },
    path::AddressPath,
    snapshot::SnapshotId,
};
use alloy_trie::{Nibbles, EMPTY_ROOT_HASH};
use std::fmt::Debug;
use std::sync::Arc;
use std::sync::RwLock;

#[derive(Debug)]
pub struct StorageEngine<P: PageManager> {
    inner: Arc<RwLock<Inner<P>>>,
}

#[derive(Debug)]
struct Inner<P: PageManager> {
    page_manager: P,
    orphan_manager: OrphanPageManager,
}

impl<P: PageManager> StorageEngine<P> {
    pub fn new(page_manager: P, orphan_manager: OrphanPageManager) -> Self {
        Self {
            inner: Arc::new(RwLock::new(Inner {
                page_manager,
                orphan_manager,
            })),
        }
    }

    pub(crate) fn unlock(&self, snapshot_id: SnapshotId) {
        self.inner
            .write()
            .unwrap()
            .orphan_manager
            .unlock(snapshot_id);
    }

    // Allocates a new page from the underlying page manager.
    // If there is an orphaned page available as of the given snapshot id,
    // it is used to allocate a new page instead.
    fn allocate_page<'p>(&self, metadata: &Metadata) -> Result<Page<'p, RW>, Error> {
        let mut inner = self.inner.write().unwrap();
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
        inner
            .page_manager
            .get_mut(metadata.snapshot_id, page_id)
            .map_err(|e| e.into())
    }

    pub fn get_account<'a, A: Account<'a>>(
        &self,
        metadata: &Metadata,
        address_path: AddressPath,
    ) -> Result<A, Error> {
        let page = self.get_page(metadata, metadata.root_subtrie_page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;
        let root_node: Node = slotted_page.get_value(0)?;
        let mut path: Nibbles = address_path.into();

        println!("path: {:?}", path);
        println!("root_node.prefix(): {:?}", root_node.prefix());
        if !path.has_prefix(&root_node.prefix()) {
            return Err(Error::InvalidPath);
        }

        path = path.slice(root_node.prefix().len()..);
        if path.is_empty() {
            let val: &[u8] = root_node.value().unwrap();
            return Ok(A::try_from(val).unwrap());
        }

        // TODO: support path traversal, not just matching the root node exactly.
        return Err(Error::InvalidPath);
    }

    pub fn set_account<'tx, A: Account<'tx>>(
        &self,
        metadata: &mut Metadata,
        address_path: AddressPath,
        account: Option<A>,
    ) -> Result<(), Error> {
        if account.is_none() {
            todo!("handle this case");
        }

        let account = account.unwrap();

        let root_subtrie_page_id = metadata.root_subtrie_page_id;
        let page = self.get_mut_clone(metadata, root_subtrie_page_id)?;
        let mut slotted_page: SlottedPage<'_, RW> = SlottedPage::try_from(page)?;
        let mut buf = vec![0; 1024];
        let new_node = Node::new(address_path.into(), account.try_into().unwrap(), &mut buf);
        if slotted_page.get_value::<Node>(0).is_err() {
            slotted_page.insert_value(new_node)?;
        } else {
            slotted_page.set_value(0, new_node)?;
        }
        let page: Page<'_, RW> = slotted_page.into();
        metadata.root_subtrie_page_id = page.page_id();
        Ok(())
    }

    // pub fn get_storage(&self, storage_path: StoragePath) -> Result<StorageValue, Error> {
    //     todo!()
    // }

    // pub fn set_storage(&mut self, storage_path: StoragePath, value: StorageValue) -> Result<(), Error> {
    //     todo!()
    // }

    pub fn commit(&self, metadata: &Metadata) -> Result<(), Error> {
        let mut inner = self.inner.write().unwrap();
        let state_root = EMPTY_ROOT_HASH;

        // First commit to ensure all changes are written before writing the new root page.
        inner.page_manager.commit(metadata.snapshot_id)?;

        let page_mut = inner
            .page_manager
            .get_mut(metadata.snapshot_id, metadata.root_page_id)
            .unwrap();
        // TODO: include the metadata in the new root page.
        let mut new_root_page = RootPage::new(page_mut, state_root);
        for orphaned_page_id in inner.orphan_manager.iter() {
            new_root_page
                .add_orphaned_page_id(*orphaned_page_id)
                .unwrap();
        }

        // Second commit to ensure the new root page is written to disk.
        inner.page_manager.commit(metadata.snapshot_id)?;

        Ok(())
    }

    pub fn rollback(&self, metadata: &Metadata) -> Result<(), Error> {
        todo!()
    }

    pub fn resize(&mut self, new_page_count: PageId) -> Result<(), Error> {
        let mut inner = self.inner.write().unwrap();
        inner.page_manager.resize(new_page_count)?;
        Ok(())
    }
}

impl<P: PageManager> Inner<P> {
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
}

#[derive(Debug)]
pub enum Error {
    PageError(PageError),
    InvalidPath,
    InvalidSnapshotId,
}

impl From<PageError> for Error {
    fn from(error: PageError) -> Self {
        Error::PageError(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::page::MmapPageManager;

    #[test]
    fn test_allocate_get_mut_clone() {
        let manager = MmapPageManager::new_anon(10, 2).unwrap();
        let orphan_manager = OrphanPageManager::new();
        let mut metadata = Metadata {
            snapshot_id: 1,
            root_page_id: 0,
            root_subtrie_page_id: 0,
        };
        let storage_engine = StorageEngine::new(manager, orphan_manager);

        let mut page = storage_engine.allocate_page(&metadata).unwrap();
        assert_eq!(page.page_id(), 2);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 1);

        page.contents_mut()[0] = 123;

        storage_engine.commit(&metadata).unwrap();
        metadata = metadata.next();

        let page = storage_engine.get_page(&metadata, 2).unwrap();
        assert_eq!(page.page_id(), 2);
        assert_eq!(page.contents()[0], 123);
        assert_eq!(page.snapshot_id(), 1);

        // cloning a page should allocate a new page and orphan the original page.
        let cloned_page = storage_engine.get_mut_clone(&metadata, 2).unwrap();
        assert_eq!(cloned_page.page_id(), 3);
        assert_eq!(cloned_page.contents()[0], 123);
        assert_eq!(cloned_page.snapshot_id(), 2);
        assert_ne!(cloned_page.page_id(), page.page_id());

        // the next allocation should not come from the orphaned page, as the snapshot id is the same as when the page was orphaned.
        let page = storage_engine.allocate_page(&metadata).unwrap();
        assert_eq!(page.page_id(), 4);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 2);

        storage_engine.commit(&metadata).unwrap();
        metadata = metadata.next();
        // the next allocation should not come from the orphaned page, as the snapshot has not been unlocked yet.
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
        let manager = MmapPageManager::new_anon(10, 2).unwrap();
        let orphan_manager = OrphanPageManager::new();
        let metadata = Metadata {
            snapshot_id: 1,
            root_page_id: 0,
            root_subtrie_page_id: 0,
        };
        let storage_engine = StorageEngine::new(manager, orphan_manager);

        let page1 = storage_engine.get_page(&metadata, 1).unwrap();

        assert_eq!(page1.contents()[0], 0);

        let mut page2 = storage_engine.get_mut_page(&metadata, 1).unwrap();
        page2.contents_mut()[0] = 123;

        storage_engine.commit(&metadata).unwrap();

        assert_eq!(page1.contents()[0], 123);
        assert_eq!(page2.contents()[0], 123);
    }
}
