use crate::{
    page::{OrphanPageManager, Page, PageError, PageId, PageManager, RootPage, RO, RW},
    snapshot::SnapshotId,
};
use alloy_trie::EMPTY_ROOT_HASH;

#[derive(Debug)]
pub struct StorageEngine<P: PageManager> {
    snapshot_id: SnapshotId,
    root_subtrie_page_id: PageId,
    root_page_id: PageId,
    page_manager: P,
    orphan_manager: OrphanPageManager,
}

impl<P: PageManager> StorageEngine<P> {
    pub fn new(
        snapshot_id: SnapshotId,
        root_subtrie_page_id: PageId,
        root_page_id: PageId,
        page_manager: P,
        orphan_manager: OrphanPageManager,
    ) -> Self {
        Self {
            snapshot_id,
            root_subtrie_page_id,
            root_page_id,
            page_manager,
            orphan_manager,
        }
    }

    pub fn snapshot_id(&self) -> SnapshotId {
        self.snapshot_id
    }

    pub(crate) fn unlock(&mut self, snapshot_id: SnapshotId) {
        self.orphan_manager.unlock(snapshot_id);
    }

    // Allocates a new page from the underlying page manager.
    // If there is an orphaned page available as of the given snapshot id,
    // it is used to allocate a new page instead.
    fn allocate_page<'p>(&mut self) -> Result<Page<'p, RW>, Error> {
        let orphaned_page_id = self.orphan_manager.get_orphaned_page_id();
        if let Some(orphaned_page_id) = orphaned_page_id {
            let mut page = self
                .page_manager
                .get_mut(self.snapshot_id, orphaned_page_id)?;
            page.contents_mut().fill(0);
            Ok(page)
        } else {
            self.page_manager
                .allocate(self.snapshot_id)
                .map_err(|e| e.into())
        }
    }

    // Retrieves a mutable clone of a page from the underlying page manager.
    // The original page is marked as orphaned and a new page is allocated, potentially from an orphaned page.
    fn get_mut_clone<'p>(&mut self, page_id: PageId) -> Result<Page<'p, RW>, Error> {
        let mut new_page = self.allocate_page()?;

        let original_page = self.page_manager.get(self.snapshot_id, page_id)?;
        self.orphan_manager
            .add_orphaned_page_id(self.snapshot_id, page_id);
        new_page
            .contents_mut()
            .copy_from_slice(original_page.contents());
        Ok(new_page)
    }

    fn get_page<'p>(&self, page_id: PageId) -> Result<Page<'p, RO>, Error> {
        self.page_manager
            .get(self.snapshot_id, page_id)
            .map_err(|e| e.into())
    }

    fn get_mut_page<'p>(&mut self, page_id: PageId) -> Result<Page<'p, RW>, Error> {
        self.page_manager
            .get_mut(self.snapshot_id, page_id)
            .map_err(|e| e.into())
    }

    // pub fn get_account(&self, address_path: AddressPath) -> Result<Account, Error> {
    //     todo!()
    // }

    // pub fn set_account(&mut self, address_path: AddressPath, account: Option<Account>) -> Result<(), Error> {
    //     todo!()
    // }

    // pub fn get_storage(&self, storage_path: StoragePath) -> Result<StorageValue, Error> {
    //     todo!()
    // }

    // pub fn set_storage(&mut self, storage_path: StoragePath, value: StorageValue) -> Result<(), Error> {
    //     todo!()
    // }

    pub fn commit(&mut self, snapshot_id: SnapshotId) -> Result<(), Error> {
        if snapshot_id <= self.snapshot_id {
            return Err(Error::InvalidSnapshotId);
        }

        let state_root = EMPTY_ROOT_HASH;

        self.page_manager.commit(snapshot_id)?;
        self.snapshot_id = snapshot_id;

        let root_page_id = (self.root_page_id + 1) % 2;
        let page_mut = self
            .page_manager
            .get_mut(self.snapshot_id, root_page_id)
            .unwrap();
        let mut new_root_page = RootPage::new(page_mut, state_root);
        for orphaned_page_id in self.orphan_manager.iter() {
            new_root_page
                .add_orphaned_page_id(*orphaned_page_id)
                .unwrap();
        }
        self.root_page_id = root_page_id;

        // Note: the new root page is not committed to disk yet.

        Ok(())
    }

    pub fn rollback(&mut self, snapshot_id: SnapshotId) -> Result<(), Error> {
        todo!()
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
    use crate::page::PAGE_SIZE;
    use memmap2::MmapMut;

    #[test]
    fn test_allocate_get_mut_clone() {
        let mmap = MmapMut::map_anon(10 * PAGE_SIZE).unwrap();
        let manager = MmapPageManager::new(mmap, 2);
        let orphan_manager = OrphanPageManager::new();
        let mut storage_engine = StorageEngine::new(1, 0, 0, manager, orphan_manager);

        let mut page = storage_engine.allocate_page().unwrap();
        assert_eq!(page.page_id(), 2);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 1);

        page.contents_mut()[0] = 123;

        storage_engine.commit(2).unwrap();

        let page = storage_engine.get_page(2).unwrap();
        assert_eq!(page.page_id(), 2);
        assert_eq!(page.contents()[0], 123);
        assert_eq!(page.snapshot_id(), 1);

        // cloning a page should allocate a new page and orphan the original page.
        let cloned_page = storage_engine.get_mut_clone(2).unwrap();
        assert_eq!(cloned_page.page_id(), 3);
        assert_eq!(cloned_page.contents()[0], 123);
        assert_eq!(cloned_page.snapshot_id(), 2);
        assert_ne!(cloned_page.page_id(), page.page_id());

        // the next allocation should not come from the orphaned page, as the snapshot id is the same as when the page was orphaned.
        let page = storage_engine.allocate_page().unwrap();
        assert_eq!(page.page_id(), 4);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 2);

        storage_engine.commit(3).unwrap();

        // the next allocation should not come from the orphaned page, as the snapshot has not been unlocked yet.
        let page = storage_engine.allocate_page().unwrap();
        assert_eq!(page.page_id(), 5);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 3);

        storage_engine.unlock(3);

        // the next allocation should come from the orphaned page because the snapshot id has increased.
        // The page data should be zeroed out.
        let page = storage_engine.allocate_page().unwrap();
        assert_eq!(page.page_id(), 2);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 3);
    }

    #[test]
    fn test_shared_page_mutability() {
        let mmap = MmapMut::map_anon(10 * PAGE_SIZE).unwrap();
        let manager = MmapPageManager::new(mmap, 2);
        let orphan_manager = OrphanPageManager::new();
        let mut storage_engine = StorageEngine::new(1, 0, 0, manager, orphan_manager);

        let page1 = storage_engine.get_page(0).unwrap();

        assert_eq!(page1.contents()[0], 0);

        let mut page2 = storage_engine.get_mut_page(0).unwrap();
        page2.contents_mut()[0] = 123;

        storage_engine.commit(3).unwrap();

        assert_eq!(page1.contents()[0], 123);
        assert_eq!(page2.contents()[0], 123);
    }
}
