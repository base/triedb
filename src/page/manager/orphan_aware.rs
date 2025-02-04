use crate::page::{Page, PageError, PageId, PageManager, PageMut, PAGE_DATA_SIZE, ReadablePage, WritablePage};
use crate::snapshot::SnapshotId;
use crate::page::orphan::OrphanPageManager;

// A page manager that is aware of orphaned pages and can allocate new pages from them.
#[derive(Debug)]
pub struct OrphanAwarePageManager<M: PageManager> {
    manager: M,
    orphan_manager: OrphanPageManager,
}

impl<M: PageManager> OrphanAwarePageManager<M> {
    // Creates a new OrphanAwarePageManager with the given page manager and orphan manager.
    pub fn new(manager: M, orphan_manager: OrphanPageManager) -> Self {
        Self { manager, orphan_manager }
    }
}

impl<M: PageManager> PageManager for OrphanAwarePageManager<M> {
    // Retrieves a page from the underlying page manager.
    fn get(&self, snapshot_id: SnapshotId, page_id: PageId) -> Result<Page<'_>, PageError> {
        self.manager.get(snapshot_id, page_id)
    }

    // Retrieves a mutable page from the underlying page manager.
    fn get_mut(&mut self, snapshot_id: SnapshotId, page_id: PageId) -> Result<PageMut<'_>, PageError> {
        self.manager.get_mut(snapshot_id, page_id)
    }

    // Retrieves a mutable clone of a page from the underlying page manager.
    // The original page is marked as orphaned and a new page is allocated, potentially from an orphaned page.
    fn get_mut_clone(&mut self, snapshot_id: SnapshotId, page_id: PageId) -> Result<PageMut<'_>, PageError> {
        let mut buf = [0; PAGE_DATA_SIZE];
        let original_page = self.get(snapshot_id, page_id)?;
        buf[..].copy_from_slice(original_page.contents());
        self.orphan_manager.add_orphaned_page_id(snapshot_id, page_id);
        let mut new_page = self.allocate(snapshot_id)?;
        new_page.contents_mut().copy_from_slice(&buf);
        Ok(new_page)
    }

    // Allocates a new page from the underlying page manager.
    // If there is an orphaned page available as of the given snapshot id,
    // it is used to allocate a new page instead.
    fn allocate(&mut self, snapshot_id: SnapshotId) -> Result<PageMut<'_>, PageError> {
        let orphaned_page_id = self.orphan_manager.get_orphaned_page_id(snapshot_id-1);
        if let Some(orphaned_page_id) = orphaned_page_id {
            let mut page = self.get_mut(snapshot_id, orphaned_page_id)?;
            page.contents_mut().fill(0);
            Ok(page)
        } else {
            self.manager.allocate(snapshot_id)
        }
    }

    // Commits the underlying page manager to disk.
    fn commit(&mut self, snapshot_id: SnapshotId) -> Result<(), PageError> {
        // TODO: commit orphaned pages to disk
        self.manager.commit(snapshot_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use memmap2::MmapMut;
    use crate::page::manager::mmap::MmapPageManager;
    use crate::page::PAGE_SIZE;

    #[test]
    fn test_allocate_get_mut_clone() {
        let mmap = MmapMut::map_anon(10*PAGE_SIZE).unwrap();
        let manager = MmapPageManager::new(mmap, 0);
        let orphan_manager = OrphanPageManager::new();
        let mut orphan_aware_manager = OrphanAwarePageManager::new(manager, orphan_manager);

        let mut page = orphan_aware_manager.allocate(1).unwrap();
        assert_eq!(page.page_id(), 0);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 1);

        page.contents_mut()[0] = 123;

        orphan_aware_manager.commit(1).unwrap();

        let page = orphan_aware_manager.get(1, 0).unwrap();
        assert_eq!(page.page_id(), 0);
        assert_eq!(page.contents()[0], 123);
        assert_eq!(page.snapshot_id(), 1);

        // cloning a page should allocate a new page and orphan the original page.
        let page = orphan_aware_manager.get_mut_clone(2, 0).unwrap();
        assert_eq!(page.page_id(), 1);
        assert_eq!(page.contents()[0], 123);
        assert_eq!(page.snapshot_id(), 2);

        // the next allocation should not come from the orphaned page, as the snapshot id is the same as when the page was orphaned.
        let page = orphan_aware_manager.allocate(2).unwrap();
        assert_eq!(page.page_id(), 2);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 2);

        orphan_aware_manager.commit(2).unwrap();

        // the next allocation should come from the orphaned page because the snapshot id has increased.
        // The page data should be zeroed out.
        let page = orphan_aware_manager.allocate(3).unwrap();
        assert_eq!(page.page_id(), 0);
        assert_eq!(page.contents()[0], 0);
        assert_eq!(page.snapshot_id(), 3);
    }
}
