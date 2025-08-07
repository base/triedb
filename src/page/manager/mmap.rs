use crate::{
    page::{manager::syncer::PageSyncer, Page, PageError, PageId, PageManagerOptions, PageMut},
    snapshot::SnapshotId,
};
use memmap2::{Advice, MmapOptions, MmapRaw};
use parking_lot::Mutex;
use std::{
    fs::File,
    io,
    path::Path,
    sync::atomic::{AtomicU32, AtomicU64, Ordering},
};

// Manages pages in a memory mapped file.
#[derive(Debug)]
pub struct PageManager {
    file: Mutex<File>,
    file_len: AtomicU64,
    page_count: AtomicU32,
    syncer: PageSyncer,
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
        let mmap = if cfg!(not(miri)) {
            let mmap = MmapOptions::new().len(mmap_len).map_raw(&file).map_err(PageError::IO)?;
            mmap.advise(Advice::Random).map_err(PageError::IO)?;
            mmap
        } else {
            MmapOptions::new().len(mmap_len).map_anon().map_err(PageError::IO)?.into()
        };

        let file_len = file.metadata().map_err(PageError::IO)?.len();
        let min_file_len = (opts.page_count as u64) * (Page::SIZE as u64);
        assert!(
            file_len >= min_file_len,
            "page_count ({}) exceeds the number of pages in the file ({})",
            opts.page_count,
            file_len / (Page::SIZE as u64)
        );

        let syncer =
            PageSyncer::new(mmap, opts.io_parallelism).map_err(PageError::ThreadPoolError)?;

        Ok(Self {
            file: Mutex::new(file),
            file_len: AtomicU64::new(file_len),
            page_count: AtomicU32::new(opts.page_count),
            syncer,
        })
    }

    #[inline]
    pub fn mmap(&self) -> &MmapRaw {
        self.syncer.mmap()
    }

    /// Returns the number of pages currently stored in the file.
    pub fn size(&self) -> u32 {
        self.page_count.load(Ordering::Relaxed)
    }

    /// Returns the maximum number of pages that can be allocated to the file.
    pub fn capacity(&self) -> u32 {
        (self.mmap().len() / Page::SIZE).min(u32::MAX as usize) as u32
    }

    /// Grows the size of the underlying file to make room for additional pages.
    ///
    /// This will increase the file size by a constant factor of 1024 pages, or a relative factor
    /// of 12.5%, whichever is greater, without exceeding the maximum capacity of the file.
    ///
    /// On success, returns the new length (in bytes) of the file.
    fn grow(&self, file: &mut File) -> Result<u64, PageError> {
        let cur_len = self.file_len.load(Ordering::Relaxed);
        let increment = (cur_len / 8).max(1024 * Page::SIZE as u64);
        let new_len = cur_len.checked_add(increment).ok_or(PageError::PageLimitReached)?;
        let new_len = new_len.min(self.mmap().len() as u64);
        if new_len <= cur_len {
            return Err(PageError::PageLimitReached);
        }

        file.set_len(new_len).map_err(PageError::IO)?;
        self.file_len.store(new_len, Ordering::Relaxed);
        Ok(new_len)
    }

    /// Ensures that the underlying file has at least `min_len` bytes, growing it if needed.
    #[inline]
    fn grow_if_needed(&self, min_len: u64) -> Result<(), PageError> {
        // `file_len` is an atomic and it's not protected by a mutex together with `file` so that,
        // in the best case when the file is large enough, we perform only a single atomic
        // operation, and zero mutex acquisitions. In the worst case, when the file needs to grow,
        // we perform additional atomic operations, but because grow adds a large number of pages
        // per call, this is rare.
        if min_len > self.file_len.load(Ordering::Relaxed) {
            // The file needs to grow.
            let mut file = self.file.lock();
            // Check again to see if another thread updated the file length before we were able to
            // acquire the lock.
            if min_len > self.file_len.load(Ordering::Relaxed) {
                // Add extra room at the end of the file. We do this in a loop, rather than
                // specifically need what we need, to (1) ensure a predictable exponential growth,
                // and (2) keep the code simple. In practice, `grow_if_needed()` will be called
                // only by `allocate()` to make room for 1 page, and `grow()` always adds at least
                // 1024 pages, so there's no need for more sophisticated code: the loop will run at
                // most once, except in extreme (and unlikely) scenarios.
                loop {
                    let new_len = self.grow(&mut file)?;
                    if new_len >= min_len {
                        break;
                    }
                }
            }
        }
        Ok(())
    }

    /// Increments the page count and returns the ID for a new page at the end of the file, along
    /// with the new page count.
    fn next_page_id(&self) -> Option<(PageId, u32)> {
        let mut old_count = self.page_count.load(Ordering::Relaxed);
        loop {
            let new_count = old_count.checked_add(1)?;
            let page_id = PageId::try_from(new_count).ok()?;
            match self.page_count.compare_exchange_weak(
                old_count,
                new_count,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Some((page_id, new_count)),
                Err(value) => old_count = value,
            }
        }
    }

    /// Retrieves a page from the memory mapped file.
    pub fn get(&self, _snapshot_id: SnapshotId, page_id: PageId) -> Result<Page<'_>, PageError> {
        if page_id > self.page_count.load(Ordering::Relaxed) {
            return Err(PageError::PageNotFound(page_id));
        }

        let offset = page_id.as_offset();
        // SAFETY: We have checked that the page fits inside the memory map.
        let data = unsafe { self.mmap().as_mut_ptr().byte_add(offset).cast() };

        // SAFETY: All memory from the memory map is accessed through `Page` or `PageMut`, thus
        // respecting the page state access memory model.
        unsafe { Page::from_ptr(page_id, data) }
    }

    /// Retrieves a mutable page from the memory mapped file.
    pub fn get_mut(
        &self,
        snapshot_id: SnapshotId,
        page_id: PageId,
    ) -> Result<PageMut<'_>, PageError> {
        if page_id > self.page_count.load(Ordering::Relaxed) {
            return Err(PageError::PageNotFound(page_id));
        }

        let offset = page_id.as_offset();
        // SAFETY: We have checked that the page fits inside the memory map.
        let data = unsafe { self.mmap().as_mut_ptr().byte_add(offset).cast() };

        // TODO: This is actually unsafe, as it's possible to call `get()` arbitrary times before
        // calling this function (this will be fixed in a future commit).
        unsafe { PageMut::from_ptr(page_id, snapshot_id, data, Some(&self.syncer)) }
    }

    /// Adds a new page.
    ///
    /// Returns an error if the memory map is not large enough.
    pub fn allocate(&self, snapshot_id: SnapshotId) -> Result<PageMut<'_>, PageError> {
        let (page_id, new_count) = self.next_page_id().ok_or(PageError::PageLimitReached)?;
        let new_len = new_count as usize * Page::SIZE;

        if new_len > self.mmap().len() {
            return Err(PageError::PageLimitReached);
        }
        self.grow_if_needed(new_len as u64)?;

        let offset = page_id.as_offset();
        // SAFETY: We have checked that the page fits inside the memory map.
        let data = unsafe { self.mmap().as_mut_ptr().byte_add(offset).cast() };

        // SAFETY:
        // - This is a newly created page at the end of the file, so we're guaranteed to have
        //   exclusive access to it. Even if another thread was calling `allocate()` at the same
        //   time, they would get a different `page_id`.
        // - All memory from the memory map is accessed through `Page` or `PageMut`, thus respecting
        //   the page state access memory model.
        unsafe { PageMut::acquire_unchecked(page_id, snapshot_id, data, Some(&self.syncer)) }
    }

    /// Syncs pages to the backing file.
    pub fn sync(&self) -> io::Result<()> {
        self.syncer.sync();
        Ok(())
    }

    /// Syncs and closes the backing file.
    pub fn close(self) -> io::Result<()> {
        self.sync()
    }
}

impl Drop for PageManager {
    fn drop(&mut self) {
        self.sync().expect("sync failed");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::page::page_id;

    #[test]
    fn test_allocate_get() {
        let manager = PageManager::options().max_pages(10).open_temp_file().unwrap();

        for i in 1..=10 {
            let i = PageId::new(i).unwrap();
            let err = manager.get(42, i).unwrap_err();
            assert!(matches!(err, PageError::PageNotFound(page_id) if page_id == i));

            let page = manager.allocate(42).unwrap();
            assert_eq!(page.id(), i);
            assert_eq!(page.contents(), &mut [0; Page::DATA_SIZE]);
            assert_eq!(page.snapshot_id(), 42);
            drop(page);

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
        let manager = PageManager::open_temp_file().unwrap();

        let mut page = manager.allocate(42).unwrap();
        assert_eq!(page.id(), page_id!(1));
        assert_eq!(page.contents(), &mut [0; Page::DATA_SIZE]);
        assert_eq!(page.snapshot_id(), 42);

        page.contents_mut()[0] = 1;
        drop(page);

        let old_page = manager.get(42, page_id!(1)).unwrap();
        assert_eq!(old_page.id(), page_id!(1));
        assert_eq!(old_page.contents()[0], 1);
        assert_eq!(old_page.snapshot_id(), 42);

        let page2 = manager.allocate(42).unwrap();
        let page3 = manager.allocate(42).unwrap();
        let page4 = manager.allocate(42).unwrap();

        assert_eq!(page2.id(), 2);
        assert_eq!(page3.id(), 3);
        assert_eq!(page4.id(), 4);

        drop(page2);
        drop(page3);
        drop(page4);

        let mut page2_mut = manager.get_mut(42, page_id!(2)).unwrap();
        assert_eq!(page2_mut.id(), 2);
        assert_eq!(page2_mut.contents()[0], 0);

        page2_mut.contents_mut()[0] = 2;
        assert_eq!(page2_mut.contents()[0], 2);
        drop(page2_mut);

        let page2 = manager.get(42, page_id!(2)).unwrap();
        assert_eq!(page2.contents()[0], 2);
    }

    #[test]
    #[cfg(not(miri))]
    fn auto_growth() {
        let snapshot = 123;

        let f = tempfile::tempfile().expect("temporary file creation failed");
        let m = PageManager::from_file(f.try_clone().unwrap()).expect("mmap creation failed");

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
    #[cfg(not(miri))]
    fn persistence() {
        let snapshot = 123;

        let f = tempfile::tempfile().expect("temporary file creation failed");
        let m = PageManager::from_file(f.try_clone().unwrap()).expect("mmap creation failed");

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
        assert_eq!(len(&f), 1024 * Page::SIZE);
        assert_eq!(read(&f, 8), (snapshot | 1 << 63).to_le_bytes());
        assert_eq!(read(&f, Page::DATA_SIZE), [0; Page::DATA_SIZE]);
        assert_eq!(read(&f, 1023 * Page::DATA_SIZE), [0; 1023 * Page::DATA_SIZE]);
        rewind(&f);

        // Write some data to the page
        p.contents_mut().iter_mut().for_each(|byte| *byte = 0xab);
        drop(p);

        assert_eq!(len(&f), 1024 * Page::SIZE);
        assert_eq!(read(&f, 8), snapshot.to_le_bytes());
        assert_eq!(read(&f, Page::DATA_SIZE), [0xab; Page::DATA_SIZE]);
        assert_eq!(read(&f, 1023 * Page::DATA_SIZE), [0; 1023 * Page::DATA_SIZE]);
        rewind(&f);

        // Repeat the test with more pages
        for new_page_id in 1..=255 {
            let mut p = m.allocate(snapshot).expect("page allocation failed");
            p.contents_mut().iter_mut().for_each(|byte| *byte = 0xab ^ (new_page_id as u8));
            drop(p);

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
