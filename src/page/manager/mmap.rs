use std::fs::File;

use crate::page::page::{RO, RW};
use crate::page::{Page, PageError, PageId, PageManager, PAGE_SIZE};
use crate::snapshot::SnapshotId;
use memmap2::MmapMut;

// Manages pages in a memory mapped file.
#[derive(Debug)]
pub struct MmapPageManager {
    mmap: MmapMut,
    file: Option<File>,
    next_page_id: PageId,
}

impl MmapPageManager {
    pub fn open(file_path: &str) -> Result<Self, PageError> {
        let file = File::options()
            .read(true)
            .write(true)
            .create(true)
            .open(file_path)
            .map_err(PageError::IO)?;
        let file_len = file.metadata().map_err(PageError::IO)?.len();
        let mmap = unsafe { MmapMut::map_mut(&file).map_err(PageError::IO)? };
        let manager = MmapPageManager::new(mmap, file, (file_len / PAGE_SIZE as u64) as PageId);
        Ok(manager)
    }

    // Creates a new MmapPageManager with the given memory mapped file.
    pub fn new(mmap: MmapMut, file: File, next_page_id: PageId) -> Self {
        if next_page_id > (mmap.len() / PAGE_SIZE) as u32 {
            panic!("next_page_id is greater than the number of pages in the memory mapped file");
        }
        Self {
            mmap,
            file: Some(file),
            next_page_id,
        }
    }

    // Creates a new MmapPageManager with an anonymous memory mapped file.
    pub(crate) fn new_anon(capacity: PageId, next_page_id: PageId) -> Result<Self, PageError> {
        let mmap = MmapMut::map_anon(capacity as usize * PAGE_SIZE).map_err(PageError::IO)?;
        Ok(Self {
            mmap,
            file: None,
            next_page_id,
        })
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
    fn get<'p>(&self, snapshot_id: SnapshotId, page_id: PageId) -> Result<Page<'p, RO>, PageError> {
        let page_data = self.page_data(page_id)?;
        Ok(Page::new_ro(page_id, page_data))
    }

    // Retrieves a mutable page from the memory mapped file.
    fn get_mut<'p>(
        &mut self,
        snapshot_id: SnapshotId,
        page_id: PageId,
    ) -> Result<Page<'p, RW>, PageError> {
        let page_data = self.page_data(page_id)?;
        Ok(Page::new_rw(page_id, page_data))
    }

    // Allocates a new page in the memory mapped file.
    fn allocate<'p>(&mut self, snapshot_id: SnapshotId) -> Result<Page<'p, RW>, PageError> {
        let (page_id, page_data) = self.allocate_page_data()?;
        Ok(Page::new_rw_with_snapshot(page_id, snapshot_id, page_data))
    }

    // Resizes the memory mapped file to the given number of pages.
    // If the file size is reduced, the file is truncated and the next page is is lowered to match the new file size.
    fn resize(&mut self, new_page_count: PageId) -> Result<(), PageError> {
        let old_len = self.mmap.len() as u64;
        let file_len = new_page_count as u64 * PAGE_SIZE as u64;
        if let Some(file) = &self.file {
            if old_len > 0 {
                self.mmap.flush().map_err(PageError::IO)?;
            }
            file.set_len(file_len).map_err(PageError::IO)?;
            let mmap =
                unsafe { MmapMut::map_mut(self.file.as_ref().unwrap()) }.map_err(PageError::IO)?;
            self.mmap = mmap;
        } else {
            self.mmap = MmapMut::map_anon(file_len as usize).map_err(PageError::IO)?;
        }
        if file_len < old_len {
            self.next_page_id = new_page_count;
        }
        Ok(())
    }

    // Commits the memory mapped file to disk.
    fn commit(&mut self, snapshot_id: SnapshotId) -> Result<(), PageError> {
        self.mmap.flush().map_err(PageError::IO)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::page::page::PAGE_DATA_SIZE;

    #[test]
    fn test_allocate_get() {
        let mut manager = MmapPageManager::new_anon(10, 0).unwrap();

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
        let mut manager = MmapPageManager::new_anon(10, 0).unwrap();

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

    #[test]
    fn test_resize_file() {
        // remove the existing file if it already exists
        let _ = std::fs::remove_file("test.mmap");

        let mut manager = MmapPageManager::open("test.mmap").unwrap();
        assert_eq!(manager.next_page_id, 0);

        // attempt to allocate, expect error because the file is empty
        let err = manager.allocate(42).unwrap_err();
        assert!(matches!(err, PageError::OutOfBounds(0)));

        manager.resize(1).unwrap();
        assert_eq!(manager.next_page_id, 0);

        let page = manager.allocate(42).unwrap();
        assert_eq!(page.page_id(), 0);
        assert_eq!(page.contents(), &mut [0; PAGE_DATA_SIZE]);
        assert_eq!(page.snapshot_id(), 42);
        assert_eq!(manager.next_page_id, 1);

        manager.commit(42).unwrap();

        // attempt to allocate again, expect error because the file is full
        let err = manager.allocate(42).unwrap_err();
        assert!(matches!(err, PageError::OutOfBounds(1)));

        manager.resize(2).unwrap();
        assert_eq!(manager.next_page_id, 1);

        let page = manager.allocate(42).unwrap();
        assert_eq!(page.page_id(), 1);
        assert_eq!(page.contents(), &mut [0; PAGE_DATA_SIZE]);
        assert_eq!(page.snapshot_id(), 42);
        assert_eq!(manager.next_page_id, 2);

        manager.commit(42).unwrap();

        // attempt to allocate again, expect error because the file is full
        let err = manager.allocate(42).unwrap_err();
        assert!(matches!(err, PageError::OutOfBounds(2)));

        let file = manager.file.as_ref().unwrap();
        let metadata = file.metadata().unwrap();
        assert_eq!(metadata.len(), 2 * PAGE_SIZE as u64);

        manager.resize(1).unwrap();
        assert_eq!(manager.next_page_id, 1);

        let file = manager.file.as_ref().unwrap();
        let metadata = file.metadata().unwrap();
        assert_eq!(metadata.len(), PAGE_SIZE as u64);

        let err = manager.allocate(42).unwrap_err();
        assert!(matches!(err, PageError::OutOfBounds(1)));

        manager.resize(10).unwrap();
        assert_eq!(manager.next_page_id, 1);

        let file = manager.file.as_ref().unwrap();
        let metadata = file.metadata().unwrap();
        assert_eq!(metadata.len(), 10 * PAGE_SIZE as u64);

        let page = manager.allocate(42).unwrap();
        assert_eq!(page.page_id(), 1);
        assert_eq!(page.contents(), &mut [0; PAGE_DATA_SIZE]);
        assert_eq!(page.snapshot_id(), 42);
        assert_eq!(manager.next_page_id, 2);

        // clean up
        let _ = std::fs::remove_file("test.mmap");
    }

    #[test]
    fn test_resize_anon() {
        let mut manager = MmapPageManager::new_anon(10, 0).unwrap();
        // allocate 10 times
        for i in 0..10 {
            let result = manager.allocate(42).unwrap();
            assert_eq!(result.page_id(), i);
        }
        // attempt to allocate, expect error
        let err = manager.allocate(42).unwrap_err();
        assert!(matches!(err, PageError::OutOfBounds(10)));
        // resize to 20
        manager.resize(20).unwrap();
        // allocate 10 more times
        for i in 10..20 {
            let result = manager.allocate(42).unwrap();
            assert_eq!(result.page_id(), i);
        }
        // attempt to allocate, expect error
        let err = manager.allocate(42).unwrap_err();
        assert!(matches!(err, PageError::OutOfBounds(20)));
    }
}
