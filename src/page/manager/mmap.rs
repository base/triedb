use memmap2::MmapMut;
use crate::page::{Page, PageError, PageId, PageManager, PageMut, PAGE_DATA_SIZE, PAGE_SIZE, ReadablePage};
use crate::snapshot::SnapshotId;

// Manages pages in a memory mapped file.
#[derive(Debug)]
pub struct MmapPageManager {
    mmap: MmapMut,
    next_page_id: PageId,
}

impl MmapPageManager {
    // Creates a new MmapPageManager with the given memory mapped file.
    pub fn new(mmap: MmapMut, next_page_id: PageId) -> Self {
        if next_page_id > (mmap.len() / PAGE_SIZE) as u32 {
            panic!("next_page_id is greater than the number of pages in the memory mapped file");
        }
        Self { mmap, next_page_id }
    }

    // Returns a mutable reference to the data of the page with the given id.
    fn page_data(&self, page_id: PageId) -> Result<&mut [u8; PAGE_SIZE], PageError> {
        if page_id >= self.next_page_id {
            return Err(PageError::PageNotFound(page_id));
        }
        let start = page_id as usize * PAGE_SIZE;
        let page_data = unsafe {
            &mut *(self.mmap.as_ptr().add(start) as *mut [u8; PAGE_SIZE])
        };
        Ok(page_data)
    }

    // Allocates a new page in the memory mapped file.
    fn allocate_page_data(&mut self) -> Result<(PageId, &mut [u8; PAGE_SIZE]), PageError> {
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
    fn get(&self, snapshot_id: SnapshotId, page_id: PageId) -> Result<Page<'_>, PageError> {
        let page_data = self.page_data(page_id)?;
        Ok(Page::new(page_id, page_data))
    }

    // Retrieves a mutable page from the memory mapped file.
    fn get_mut(&mut self, snapshot_id: SnapshotId, page_id: PageId) -> Result<PageMut<'_>, PageError> {
        let page_data = self.page_data(page_id)?;
        Ok(PageMut::new(page_id, snapshot_id, page_data))
    }

    // Retrieves a mutable clone of a page from the memory mapped file.
    fn get_mut_clone(&mut self, snapshot_id: SnapshotId, page_id: PageId) -> Result<PageMut<'_>, PageError> {
        let mut buf = [0; PAGE_DATA_SIZE];
        let old_page = self.get(snapshot_id, page_id)?;
        buf[..].copy_from_slice(old_page.contents());
        let (new_page_id, new_page_data) = self.allocate_page_data()?;
        new_page_data.copy_from_slice(&buf);
        Ok(PageMut::new(new_page_id, snapshot_id, new_page_data))
    }

    // Allocates a new page in the memory mapped file.
    fn allocate(&mut self, snapshot_id: SnapshotId) -> Result<PageMut<'_>, PageError> {
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
    use crate::page::{page::PAGE_DATA_SIZE, WritablePage};

    #[test]
    fn test_allocate_get() {
        let mmap = MmapMut::map_anon(10*PAGE_SIZE).unwrap();
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
    fn test_allocate_get_mut_clone() {
        let mmap = MmapMut::map_anon(10*PAGE_SIZE).unwrap();
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

        let mut new_page = manager.get_mut_clone(42, 0).unwrap();
        assert_eq!(new_page.page_id(), 1);
        assert_eq!(new_page.contents()[0], 1);
        assert_eq!(new_page.snapshot_id(), 42);

        new_page.contents_mut()[0] = 2;
        manager.commit(42).unwrap();

        let old_page = manager.get(42, 0).unwrap();
        assert_eq!(old_page.page_id(), 0);
        assert_eq!(old_page.contents()[0], 1);
        assert_eq!(old_page.snapshot_id(), 42);

        let new_page = manager.get(42, 1).unwrap();
        assert_eq!(new_page.page_id(), 1);
        assert_eq!(new_page.contents()[0], 2);
        assert_eq!(new_page.snapshot_id(), 42);

    }
}
