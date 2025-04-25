use crate::{
    page::{Page, PageError, PageId, PageManagerOptions, PageMut},
    snapshot::SnapshotId,
};
use memmap2::{Advice, MmapMut, MmapOptions};
use std::{fs::File, path::Path};

// Manages pages in a memory mapped file.
#[derive(Debug)]
pub struct PageManager {
    mmap: MmapMut,
    file: File,
    file_len: u64,
    page_count: u32,
}

impl PageManager {
    pub fn options() -> PageManagerOptions {
        PageManagerOptions::new()
    }

    pub fn open(path: impl AsRef<Path>) -> Result<Self, PageError> {
        Self::options().open(path)
    }

    pub fn from_file(file: File) -> Result<Self, PageError> {
        Self::options().wrap(file)
    }

    #[cfg(test)]
    pub fn open_temp_file() -> Result<Self, PageError> {
        Self::options().open_temp_file()
    }

    pub(super) fn open_with_options(
        opts: &PageManagerOptions,
        path: impl AsRef<Path>,
    ) -> Result<Self, PageError> {
        let file = opts.open_options.open(path).map_err(PageError::IO)?;
        Self::from_file_with_options(opts, file)
    }

    pub(super) fn from_file_with_options(
        opts: &PageManagerOptions,
        file: File,
    ) -> Result<Self, PageError> {
        // Allocate a memory map as large as possible, so that remapping will never be needed. If
        // `opts.max_page == PageId::MAX == 2 ** 32 - 1` and `Page::SIZE == 2 ** 12 == 4096`, then
        // we are requesting `2 ** 44` bytes of memory.
        //
        // Allocating such a large memory map is does not actually allocate any memory, nor causes
        // the backing file to grow to match the memory map size. It simply reserves the required
        // address space.
        //
        // This is safe and sound on 64-bit systems:
        //
        // - The size of the memory map may be larger than the amount of memory on the system. The
        //   kernel will take care of loading/unloading pages as needed.
        // - On systems where the virtual address space is 48 bits, there is room for *at least* 16
        //   of such contiguous memory maps, which is more than enough for a single process.
        //
        // This can fail if:
        //
        // - This is running on a 32-bit system (but this should not be supported).
        // - The process memory is highly fragmented.
        // - An rlimit is limiting the maximum memory that the process can obtain.
        // - Many `PageManager` structs are constructed in parallel (this can happen in tests, but
        //   should not happen in real-world application).
        //
        // Note that even if the memory map has a certain size, reading/writing to it still
        // requires the backing file to be large enough; failure to do so will result in a SIGBUS.
        let mmap_len = (opts.max_pages as usize) * Page::SIZE;

        // SAFETY: we assume that we have full ownership of the file, even though in practice
        // there's no way to guarantee it
        let mmap =
            unsafe { MmapOptions::new().len(mmap_len).map_mut(&file).map_err(PageError::IO)? };
        mmap.advise(Advice::Random).map_err(PageError::IO)?;

        let file_len = file.metadata().map_err(PageError::IO)?.len();
        let min_file_len = (opts.page_count as u64) * (Page::SIZE as u64);
        assert!(
            file_len >= min_file_len,
            "page_count ({}) exceeds the number of pages in the file ({})",
            opts.page_count,
            file_len / (Page::SIZE as u64)
        );

        Ok(Self { mmap, file, file_len, page_count: opts.page_count })
    }

    /// Returns the number of pages currently stored in the file.
    pub fn size(&self) -> u32 {
        self.page_count
    }

    /// Returns the maximum number of pages that can be allocated to the file.
    pub fn capacity(&self) -> u32 {
        (self.mmap.len() / Page::SIZE).min(u32::MAX as usize) as u32
    }

    // Returns a mutable reference to the data of the page with the given id.
    fn page_data<'p>(&self, page_id: PageId) -> Result<&'p mut [u8; Page::SIZE], PageError> {
        if page_id > self.page_count {
            return Err(PageError::PageNotFound(page_id));
        }
        let start = page_id.as_offset();
        let page_data = unsafe { &mut *(self.mmap.as_ptr().add(start) as *mut [u8; Page::SIZE]) };
        Ok(page_data)
    }

    // Allocates a new page in the memory mapped file.
    fn allocate_page_data<'p>(&mut self) -> Result<(PageId, &'p mut [u8; Page::SIZE]), PageError> {
        let new_count = self.page_count.checked_add(1).ok_or(PageError::PageLimitReached)?;
        let page_id = PageId::try_from(new_count).map_err(|_| PageError::PageLimitReached)?;
        let new_len = new_count as usize * Page::SIZE;

        if new_len > self.mmap.len() {
            return Err(PageError::PageLimitReached);
        }
        if new_len as u64 > self.file_len {
            self.grow()?;
        }

        self.page_count += 1;
        let page_data = self.page_data(page_id)?;
        page_data.fill(0);
        Ok((page_id, page_data))
    }

    /// Grows the size of the underlaying file (if any) to make room for additional pages.
    ///
    /// This will increase the file size by a constant factor of 1024, or a relative factor of
    /// 12.5%, whichever is greater, without exceeding the maximum capacity of the file.
    ///
    /// If this `PageManager` is not backed by any file, then this method returns an error.
    fn grow(&mut self) -> Result<(), PageError> {
        let cur_len = self.file_len;
        let increment = (cur_len / 8).max(1024 * Page::SIZE as u64);
        let new_len = cur_len + increment;
        let new_len = new_len.min(self.mmap.len() as u64);

        assert!(new_len > cur_len, "reached max capacity");

        self.file.set_len(new_len).map_err(PageError::IO)?;
        self.file_len = new_len;
        Ok(())
    }

    /// Retrieves a page from the memory mapped file.
    pub fn get<'p>(
        &self,
        _snapshot_id: SnapshotId,
        page_id: PageId,
    ) -> Result<Page<'p>, PageError> {
        let page_data = self.page_data(page_id)?;
        Ok(Page::new(page_id, page_data))
    }

    /// Retrieves a mutable page from the memory mapped file.
    pub fn get_mut<'p>(
        &mut self,
        _snapshot_id: SnapshotId,
        page_id: PageId,
    ) -> Result<PageMut<'p>, PageError> {
        let page_data = self.page_data(page_id)?;
        Ok(PageMut::new(page_id, page_data))
    }

    /// Adds a new page.
    ///
    /// Returns an error if the memory map is not large enough.
    pub fn allocate<'p>(&mut self, snapshot_id: SnapshotId) -> Result<PageMut<'p>, PageError> {
        let (page_id, page_data) = self.allocate_page_data()?;
        Ok(PageMut::with_snapshot(page_id, snapshot_id, page_data))
    }

    /// Syncs pages to the backing file.
    pub fn commit(&mut self) -> Result<(), PageError> {
        self.mmap.flush().map_err(PageError::IO)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::page::page_id;

    #[test]
    fn test_allocate_get() {
        let mut manager = PageManager::options().max_pages(10).open_temp_file().unwrap();

        for i in 1..=10 {
            let i = PageId::new(i).unwrap();
            let err = manager.get(42, i).unwrap_err();
            assert!(matches!(err, PageError::PageNotFound(page_id) if page_id == i));

            let page = manager.allocate(42).unwrap();
            assert_eq!(page.id(), i);
            assert_eq!(page.contents(), &mut [0; Page::DATA_SIZE]);
            assert_eq!(page.snapshot_id(), 42);

            let page = manager.get(42, i).unwrap();
            assert_eq!(page.id(), i);
            assert_eq!(page.contents(), &mut [0; Page::DATA_SIZE]);
            assert_eq!(page.snapshot_id(), 42);
        }

        let err = manager.allocate(42).unwrap_err();
        assert!(matches!(err, PageError::PageLimitReached));
    }

    #[test]
    fn test_allocate_get_mut() {
        let mut manager = PageManager::open_temp_file().unwrap();

        let mut page = manager.allocate(42).unwrap();
        assert_eq!(page.id(), page_id!(1));
        assert_eq!(page.contents(), &mut [0; Page::DATA_SIZE]);
        assert_eq!(page.snapshot_id(), 42);

        page.contents_mut()[0] = 1;

        manager.commit().unwrap();

        let old_page = manager.get(42, page_id!(1)).unwrap();
        assert_eq!(old_page.id(), page_id!(1));
        assert_eq!(old_page.contents()[0], 1);
        assert_eq!(old_page.snapshot_id(), 42);

        let page1 = manager.allocate(42).unwrap();
        let page2 = manager.allocate(42).unwrap();
        let page3 = manager.allocate(42).unwrap();

        assert_ne!(page1.id(), page2.id());
        assert_ne!(page1.id(), page3.id());
        assert_ne!(page2.id(), page3.id());

        let mut page1_mut = manager.get_mut(42, page1.id()).unwrap();
        assert_eq!(page1_mut.id(), page1.id());
        assert_eq!(page1_mut.contents()[0], 0);

        page1_mut.contents_mut()[0] = 2;

        assert_eq!(page1_mut.contents()[0], 2);

        manager.commit().unwrap();

        let page1 = manager.get(42, page1.id()).unwrap();
        assert_eq!(page1.contents()[0], 2);
    }

    #[test]
    fn auto_growth() {
        let snapshot = 123;

        let f = tempfile::tempfile().expect("temporary file creation failed");
        let mut m = PageManager::from_file(f.try_clone().unwrap()).expect("mmap creation failed");

        fn len(f: &File) -> usize {
            f.metadata().expect("fetching file metadata failed").len().try_into().unwrap()
        }

        // No page has been allocated; file should be empty
        assert_eq!(len(&f), 0);

        // Allocate a page; verify that the size of the file grew by `1024 * Page::SIZE` (the
        // minimum growth factor)

        // For the first 8 * 1024 pages, the automatic growth should be of a constant factor of
        // `1024 * Page::SIZE`
        for i in 0..8 {
            for j in 0..1024 {
                let p = m.allocate(snapshot).expect("page allocation failed");
                assert_eq!(p.id().as_usize(), 1 + i * 1024 + j);
                assert_eq!(len(&f), (i + 1) * 1024 * Page::SIZE);
            }
        }

        // From this point on, the automatic growth should be 12.5% (1/8).
        for id in (1 + 8 * 1024)..=(9 * 1024) {
            let p = m.allocate(snapshot).expect("page allocation failed");
            assert_eq!(p.id(), id);
            assert_eq!(len(&f), 9 * 1024 * Page::SIZE);
        }
        for id in (1 + 9 * 1024)..=10368 {
            let p = m.allocate(snapshot).expect("page allocation failed");
            assert_eq!(p.id(), id);
            assert_eq!(len(&f), 10368 * Page::SIZE);
        }
        for id in (1 + 10368)..=11664 {
            let p = m.allocate(snapshot).expect("page allocation failed");
            assert_eq!(p.id(), id);
            assert_eq!(len(&f), 11664 * Page::SIZE);
        }
    }

    #[test]
    fn persistence() {
        let snapshot = 123;

        let f = tempfile::tempfile().expect("temporary file creation failed");
        let mut m = PageManager::from_file(f.try_clone().unwrap()).expect("mmap creation failed");

        fn len(f: &File) -> usize {
            f.metadata().expect("fetching file metadata failed").len().try_into().unwrap()
        }

        fn read(mut f: &File, n: usize) -> Vec<u8> {
            use std::io::Read;
            let mut buf = vec![0; n];
            f.read_exact(&mut buf).expect("read failed");
            buf
        }

        fn rewind(mut f: &File) {
            use std::io::Seek;
            f.rewind().expect("rewind failed");
        }

        // No page has been allocated; file should be empty
        assert_eq!(len(&f), 0);

        // Allocate a page; verify that the size of the file grew by `1024 * Page::SIZE` (the
        // minimum growth factor) and that the file contents are as expected
        let mut p = m.allocate(snapshot).expect("page allocation failed");
        m.commit().expect("commit failed");
        assert_eq!(len(&f), 1024 * Page::SIZE);
        assert_eq!(read(&f, 8), snapshot.to_le_bytes());
        assert_eq!(read(&f, Page::DATA_SIZE), [0; Page::DATA_SIZE]);
        assert_eq!(read(&f, 1023 * Page::DATA_SIZE), [0; 1023 * Page::DATA_SIZE]);
        rewind(&f);

        // Write some data to the page
        p.contents_mut().iter_mut().for_each(|byte| *byte = 0xab);
        m.commit().expect("commit failed");
        assert_eq!(len(&f), 1024 * Page::SIZE);
        assert_eq!(read(&f, 8), snapshot.to_le_bytes());
        assert_eq!(read(&f, Page::DATA_SIZE), [0xab; Page::DATA_SIZE]);
        assert_eq!(read(&f, 1023 * Page::DATA_SIZE), [0; 1023 * Page::DATA_SIZE]);
        rewind(&f);

        // Repeat the test with more pages
        for new_page_id in 1..=255 {
            let mut p = m.allocate(snapshot).expect("page allocation failed");
            p.contents_mut().iter_mut().for_each(|byte| *byte = 0xab ^ (new_page_id as u8));
            m.commit().expect("commit failed");

            assert_eq!(len(&f), 1024 * Page::SIZE);

            for stored_page_id in 0..=new_page_id {
                assert_eq!(read(&f, 8), snapshot.to_le_bytes());
                assert_eq!(
                    read(&f, Page::DATA_SIZE),
                    [0xab ^ (stored_page_id as u8); Page::DATA_SIZE]
                );
            }

            rewind(&f);
        }
    }
}
