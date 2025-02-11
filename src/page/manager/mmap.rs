use std::fs::File;

use crate::page::{Page, PageError, PageId, PageManager, PageMut, PAGE_SIZE};
use crate::snapshot::SnapshotId;
use memmap2::MmapMut;

// Manages pages in a memory mapped file.
#[derive(Debug)]
pub struct MmapPageManager {
    mmap: MmapMut,
    next_page_id: PageId,
}

impl MmapPageManager {
    pub fn open(file_path: &str) -> Result<Self, PageError> {
        let file = File::open(file_path).map_err(PageError::IO)?;
        let file_len = file.metadata().map_err(PageError::IO)?.len();
        let mmap = unsafe { MmapMut::map_mut(&file).map_err(PageError::IO)? };
        let manager = MmapPageManager::new(mmap, (file_len / PAGE_SIZE as u64) as PageId);
        Ok(manager)
    }

    // Creates a new MmapPageManager with the given memory mapped file.
    pub fn new(mmap: MmapMut, next_page_id: PageId) -> Self {
        if next_page_id > (mmap.len() / PAGE_SIZE) as u32 {
            panic!("next_page_id is greater than the number of pages in the memory mapped file");
        }
        Self { mmap, next_page_id }
    }

    // Returns a mutable reference to the data of the page with the given id.
    fn page_data<'p>(&self, page_id: PageId) -> Result<&'p mut [u8; PAGE_SIZE], PageError> {
        if page_id >= self.next_page_id {
            return Err(PageError::PageNotFound(page_id));
        }
        let start = page_id as usize * PAGE_SIZE;
        let page_data = unsafe { &mut *(self.mmap.as_ptr().add(start) as *mut [u8; PAGE_SIZE]) };
        Ok(page_data)
    }

    // Allocates a new page in the memory mapped file.
    fn allocate_page_data<'p>(&mut self) -> Result<(PageId, &'p mut [u8; PAGE_SIZE]), PageError> {
        let page_id = self.next_page_id;

        if (page_id + 1) as usize * PAGE_SIZE > self.mmap.len() {
            return Err(PageError::OutOfBounds(page_id));
        }

        self.next_page_id += 1;
        let page_data = self.page_data(page_id)?;
        page_data.fill(0);
        Ok((page_id, page_data))
    }
}

impl PageManager for MmapPageManager {
    // Retrieves a page from the memory mapped file.
    fn get<'p>(&self, snapshot_id: SnapshotId, page_id: PageId) -> Result<Page<'p>, PageError> {
        let page_data = self.page_data(page_id)?;
        Ok(Page::new(page_id, page_data))
    }

    // Retrieves a mutable page from the memory mapped file.
    fn get_mut<'p>(
        &mut self,
        snapshot_id: SnapshotId,
        page_id: PageId,
    ) -> Result<PageMut<'p>, PageError> {
        let page_data = self.page_data(page_id)?;
        Ok(PageMut::new(page_id, snapshot_id, page_data))
    }

    // Allocates a new page in the memory mapped file.
    fn allocate<'p>(&mut self, snapshot_id: SnapshotId) -> Result<PageMut<'p>, PageError> {
        let (page_id, page_data) = self.allocate_page_data()?;
        Ok(PageMut::new(page_id, snapshot_id, page_data))
    }

    // Commits the memory mapped file to disk.
    fn commit(&mut self, snapshot_id: SnapshotId) -> Result<(), PageError> {
        self.mmap.flush().map_err(PageError::IO)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::page::{page::PAGE_DATA_SIZE, ReadablePage, WritablePage};

    #[test]
    fn test_allocate_get() {
        let mmap = MmapMut::map_anon(10 * PAGE_SIZE).unwrap();
        let mut manager = MmapPageManager::new(mmap, 0);

        for i in 0..10 {
            let err = manager.get(42, i).unwrap_err();
            assert!(matches!(err, PageError::PageNotFound(page_id) if page_id == i));

            let page = manager.allocate(42).unwrap();
            assert_eq!(page.page_id(), i);
            assert_eq!(page.contents(), &mut [0; PAGE_DATA_SIZE]);
            assert_eq!(page.snapshot_id(), 42);

            let page = manager.get(42, i).unwrap();
            assert_eq!(page.page_id(), i);
            assert_eq!(page.contents(), &mut [0; PAGE_DATA_SIZE]);
            assert_eq!(page.snapshot_id(), 42);
        }

        let err = manager.allocate(42).unwrap_err();
        assert!(matches!(err, PageError::OutOfBounds(10)));
    }

    #[test]
    fn test_allocate_get_mut() {
        let mmap = MmapMut::map_anon(10 * PAGE_SIZE).unwrap();
        let mut manager = MmapPageManager::new(mmap, 0);

        let mut page = manager.allocate(42).unwrap();
        assert_eq!(page.page_id(), 0);
        assert_eq!(page.contents(), &mut [0; PAGE_DATA_SIZE]);
        assert_eq!(page.snapshot_id(), 42);

        page.contents_mut()[0] = 1;

        manager.commit(42).unwrap();

        let old_page = manager.get(42, 0).unwrap();
        assert_eq!(old_page.page_id(), 0);
        assert_eq!(old_page.contents()[0], 1);
        assert_eq!(old_page.snapshot_id(), 42);

        let page1 = manager.allocate(42).unwrap();
        let page2 = manager.allocate(42).unwrap();
        let page3 = manager.allocate(42).unwrap();

        assert_ne!(page1.page_id(), page2.page_id());
        assert_ne!(page1.page_id(), page3.page_id());
        assert_ne!(page2.page_id(), page3.page_id());

        let mut page1_mut = manager.get_mut(42, page1.page_id()).unwrap();
        assert_eq!(page1_mut.page_id(), page1.page_id());
        assert_eq!(page1_mut.contents()[0], 0);

        page1_mut.contents_mut()[0] = 2;

        assert_eq!(page1_mut.contents()[0], 2);

        manager.commit(42).unwrap();

        let page1 = manager.get(42, page1.page_id()).unwrap();
        assert_eq!(page1.contents()[0], 2);
    }
}
