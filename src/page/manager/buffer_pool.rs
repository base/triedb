use std::{
    collections::VecDeque,
    ffi::CString,
    fs::File,
    io::{self, IoSlice, Read, Seek, SeekFrom, Write},
    os::fd::FromRawFd,
    path::Path,
    sync::atomic::{AtomicU32, AtomicU64, Ordering},
};

use dashmap::DashMap;
use evict::{EvictionPolicy, LruKReplacer, LruReplacer};
use parking_lot::Mutex;

use crate::{
    page::{Page, PageError, PageId, PageManagerTrait, PageMut},
    snapshot::SnapshotId,
};

#[derive(Debug, Clone)]
struct Frame {
    ptr: *mut [u8; Page::SIZE],
}

// SAFETY: Frame contains a pointer to heap-allocated memory that we own exclusively.
// The memory is allocated via Box and we manage its lifetime, so it's safe to send
// between threads.
unsafe impl Send for Frame {}
unsafe impl Sync for Frame {}

#[derive(Debug)]
struct FrameHeader {
    frame_id: FrameId,
    pin_count: usize,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct FrameId(u32);

#[derive(Debug)]
struct DiskScheduler {}

pub struct BufferPoolManagerOptions {
    pub(super) num_frames: u32,
    pub(super) page_count: u32,
}

const DEFAULT_NUM_FRAMES: u32 = 1024 * 1024 * 2;

impl BufferPoolManagerOptions {
    pub fn new() -> Self {
        Self { num_frames: DEFAULT_NUM_FRAMES, page_count: 0 }
    }

    pub fn num_frames(&mut self, num_frames: u32) -> &mut Self {
        self.num_frames = num_frames;
        self
    }

    pub fn page_count(&mut self, page_count: u32) -> &mut Self {
        self.page_count = page_count;
        self
    }
}

// TODO: could have a list of dirty pages
#[derive(Debug)]
pub struct BufferPoolManager {
    num_frames: u32,
    page_count: AtomicU32,
    file_len: AtomicU64,
    file: File,
    frames: Vec<Frame>, /* list of frames that hold pages' data, indexed by frame id with fix
                         * num_frames size */
    page_table: DashMap<PageId, FrameHeader>, /* mapping between page id and buffer pool frames,
                                               * indexed by page id with fix num_frames size */
    free_frames: Mutex<VecDeque<FrameId>>, /* list of free frames that do not hold any pages'
                                            * data, with fix num_frames size */
    dirty_frames: Mutex<Vec<(FrameId, PageId)>>, /* list of dirty frames that need to be flushed
                                                  * to disk, with fix num_frames size */
    disk_scheduler: DiskScheduler, /* the scheduler to schedule disk flushing operations */
    lru_replacer: LruReplacer<PageId>, /* the replacer to find unpinned/candidate pages for
                                    * eviction */
}

impl BufferPoolManager {
    pub fn options() -> BufferPoolManagerOptions {
        BufferPoolManagerOptions::new()
    }

    pub fn open(path: impl AsRef<Path>) -> Result<Self, PageError> {
        let opts = BufferPoolManagerOptions::new();
        Self::open_with_options(&opts, path)
    }

    pub fn open_with_options(
        opts: &BufferPoolManagerOptions,
        path: impl AsRef<Path>,
    ) -> Result<Self, PageError> {
        let path_cstr = CString::new(path.as_ref().to_string_lossy().as_bytes())
            .map_err(|_| PageError::InvalidValue)?;
        // Use O_DIRECT on Linux for better performance, but not available on macOS
        #[cfg(target_os = "linux")]
        let flags = libc::O_RDWR | libc::O_CREAT | libc::O_DIRECT;
        #[cfg(not(target_os = "linux"))]
        let flags = libc::O_RDWR | libc::O_CREAT;
        let fd = unsafe { libc::open(path_cstr.as_ptr(), flags, 0o644) };
        if fd == -1 {
            return Err(PageError::IO(io::Error::last_os_error()));
        }
        let file = unsafe { File::from_raw_fd(fd) };

        Self::from_file_with_options(opts, file)
    }

    pub(super) fn from_file_with_options(
        opts: &BufferPoolManagerOptions,
        file: File,
    ) -> Result<Self, PageError> {
        let num_frames = opts.num_frames;
        let page_count = AtomicU32::new(opts.page_count);
        let file_len = AtomicU64::new(file.metadata().map_err(PageError::IO)?.len());
        let page_table = DashMap::with_capacity(num_frames as usize);
        let mut frames = Vec::with_capacity(num_frames as usize);
        for _ in 0..num_frames {
            let boxed_array = Box::new([0; Page::SIZE]);
            let ptr = Box::into_raw(boxed_array);
            frames.push(Frame { ptr });
        }
        let dirty_frames = Mutex::new(Vec::with_capacity(num_frames as usize));
        let free_frames = Mutex::new((0..num_frames).map(FrameId).collect::<VecDeque<_>>());
        let disk_scheduler = DiskScheduler {};
        let lru_replacer = LruReplacer::new(num_frames as usize);

        Ok(BufferPoolManager {
            num_frames,
            page_count,
            file_len,
            frames,
            page_table,
            free_frames,
            dirty_frames,
            disk_scheduler,
            lru_replacer,
            file,
        })
    }

    fn next_page_id(&self) -> Option<(PageId, u32)> {
        // TODO: could have race condition here
        let old_count = self.page_count.load(Ordering::Relaxed);
        let new_count = old_count.checked_add(1)?;
        let page_id = PageId::try_from(new_count).ok()?;
        self.page_count.store(new_count, Ordering::Relaxed);
        Some((page_id, new_count))
    }

    fn get_free_frame(&self) -> Option<FrameId> {
        let mut free_frames = self.free_frames.lock();
        let fr = free_frames.pop_front();
        match fr {
            Some(frame_id) => Some(frame_id),
            None => {
                let evicted_page = self.lru_replacer.evict();
                if let Some(page_id) = evicted_page {
                    self.page_table.remove(&page_id).map(|(_, frame_header)| frame_header.frame_id)
                } else {
                    None
                }
            }
        }
    }

    fn grow_if_needed(&self, min_len: u32) -> Result<(), PageError> {
        // TODO: implement this
        Ok(())
    }

    // Access a page, update the cache advisory
    // fn access_page(&self, page_id: PageId, pin: bool) -> Result<(), PageError> {
    // let mut lru_replacer = self.lru_replacer.lock();
    // let evicted = lru_replacer.accessed_reuse_buffer(page_id.as_u64(), 1);
    // if !evicted.is_empty() {
    //     let mut free_frames = self.free_frames.lock();
    //     evicted.iter().for_each(|(page_id, _)| {
    //         let page_id = PageId::try_from(*page_id as u32).unwrap();
    //         let frame = self.page_table.remove(&page_id);
    //         if let Some((_, frame_header)) = frame {
    //             free_frames.push_back(frame_header.frame_id);
    //         }
    //     });
    //     lru_replacer.reset_internal_access_buffer();
    // }
    // }
}

impl PageManagerTrait for BufferPoolManager {
    /// Retrieves a page from the buffer pool.
    fn get(&self, _snapshot_id: SnapshotId, page_id: PageId) -> Result<Page<'_>, PageError> {
        if page_id > self.page_count.load(Ordering::Relaxed) {
            return Err(PageError::PageNotFound(page_id));
        }
        let cached_page = self.page_table.get(&page_id).map(|frame_header| {
            let frame = &self.frames[frame_header.frame_id.0 as usize];
            unsafe { Page::from_ptr(page_id, frame.ptr) }
        });
        if let Some(page) = cached_page {
            return page;
        }

        // Otherwise, need to load the page from disk
        let mut file = &self.file;
        let frame_id = self.get_free_frame().ok_or(PageError::OutOfMemory)?;

        file.seek(SeekFrom::Start(page_id.as_offset() as u64)).map_err(PageError::IO)?;
        let buf: *mut [u8; Page::SIZE] = self.frames[frame_id.0 as usize].ptr;
        unsafe {
            file.read_exact(&mut *buf).map_err(PageError::IO)?;
        }
        self.page_table.insert(page_id, FrameHeader { frame_id, pin_count: 0 });
        // self.access_page(page_id);
        self.lru_replacer.touch(page_id).map_err(|_| PageError::EvictionPolicy)?;

        unsafe { Page::from_ptr(page_id, buf) }
    }

    /// Retrieves a mutable page from the buffer pool.
    fn get_mut(&self, snapshot_id: SnapshotId, page_id: PageId) -> Result<PageMut<'_>, PageError> {
        if page_id > self.page_count.load(Ordering::Relaxed) {
            return Err(PageError::PageNotFound(page_id));
        }
        let cached_page = self.page_table.get(&page_id).map(|frame_header| {
            let frame = &self.frames[frame_header.frame_id.0 as usize];
            unsafe { PageMut::from_ptr(page_id, snapshot_id, frame.ptr) }
        });

        if let Some(page) = cached_page {
            return page;
        }

        // Otherwise, need to load the page from disk
        let mut file = &self.file;
        let frame_id = self.get_free_frame().ok_or(PageError::OutOfMemory)?;

        file.seek(SeekFrom::Start(page_id.as_offset() as u64)).map_err(PageError::IO)?;
        let buf: *mut [u8; Page::SIZE] = self.frames[frame_id.0 as usize].ptr;
        unsafe {
            file.read_exact(&mut *buf).map_err(PageError::IO)?;
        }
        self.page_table.insert(page_id, FrameHeader { frame_id, pin_count: 0 });
        self.dirty_frames.lock().push((frame_id, page_id));
        // self.access_page(page_id);
        self.lru_replacer.pin(page_id).map_err(|_| PageError::EvictionPolicy)?;

        unsafe { PageMut::from_ptr(page_id, snapshot_id, buf) }
    }

    /// Adds a new page to the buffer pool.
    ///
    /// Returns an error if the buffer pool is full.
    fn allocate(&self, snapshot_id: SnapshotId) -> Result<PageMut<'_>, PageError> {
        let frame_id = self.get_free_frame().ok_or(PageError::OutOfMemory)?;
        let (page_id, new_count) = self.next_page_id().ok_or(PageError::PageLimitReached)?;

        // grow the file if needed
        self.grow_if_needed(new_count * Page::SIZE as u32)?;

        self.page_table.insert(page_id, FrameHeader { frame_id: frame_id.clone(), pin_count: 0 });
        self.dirty_frames.lock().push((frame_id, page_id));
        // self.access_page(page_id);
        self.lru_replacer.pin(page_id).map_err(|_| PageError::EvictionPolicy)?;

        let data = self.frames[frame_id.0 as usize].ptr;
        unsafe { PageMut::acquire_unchecked(page_id, snapshot_id, data) }
    }

    /// Syncs the buffer pool to the file.
    fn sync(&self) -> io::Result<()> {
        let mut file = &self.file;
        // get all value at dirty_frames

        let mut dirty_pages = self.dirty_frames.lock();
        dirty_pages.sort_by_key(|(_, page_id)| page_id.as_offset());

        // Group contigous pages together
        let mut current_offset = None;
        let mut batch: Vec<IoSlice> = Vec::new();

        for (frame_id, page_id) in dirty_pages.iter() {
            let offset = page_id.as_offset() as u64;
            if let Some(prev_offset) = current_offset {
                if offset != prev_offset + (batch.len() * Page::SIZE) as u64 {
                    // write the current batch
                    file.seek(SeekFrom::Start(prev_offset))?;
                    file.write_vectored(&batch)?;
                    batch.clear();
                }
            }
            if batch.is_empty() {
                current_offset = Some(offset);
            }
            let frame = &self.frames[frame_id.0 as usize];
            unsafe {
                let page_data = std::slice::from_raw_parts(frame.ptr as *const u8, Page::SIZE);
                batch.push(IoSlice::new(page_data));
            }
        }
        // Write final batch
        if !batch.is_empty() {
            file.seek(SeekFrom::Start(current_offset.unwrap()))?;
            file.write_vectored(&batch)?;
        }
        file.flush()?;
        for (_, page_id) in dirty_pages.iter() {
            self.lru_replacer.unpin(*page_id).map_err(|e| {
                io::Error::new(io::ErrorKind::Other, format!("eviction policy error: {:?}", e))
            })?;
        }
        dirty_pages.clear();
        Ok(())
    }

    /// Syncs and closes the buffer pool.
    fn close(self: Box<Self>) -> io::Result<()> {
        (*self).sync()
    }

    fn size(&self) -> u32 {
        self.page_count.load(Ordering::Relaxed)
    }

    fn capacity(&self) -> u32 {
        self.num_frames as u32
    }
}

impl Drop for BufferPoolManager {
    fn drop(&mut self) {
        self.sync().expect("sync failed");
    }
}

#[cfg(test)]
mod tests {
    use crate::page_id;

    use super::*;
    use std::io::Seek;

    fn len(f: &File) -> usize {
        f.metadata().expect("fetching file metadata failed").len().try_into().unwrap()
    }

    fn read(mut f: &File, n: usize) -> Vec<u8> {
        use std::io::Read;
        let mut buf = vec![0; n];
        f.read_exact(&mut buf).expect("read failed");
        buf
    }

    fn seek(mut f: &File, offset: u64) {
        f.seek(SeekFrom::Start(offset)).expect("seek failed");
    }

    #[test]
    fn test_allocate_cache() {
        let snapshot = 1234;
        let f = tempfile::tempfile().expect("temporary file creation failed");
        let opts = BufferPoolManagerOptions::new();
        let m = BufferPoolManager::from_file_with_options(&opts, f.try_clone().unwrap())
            .expect("mmap creation failed");

        for i in 1..=10 {
            let i = PageId::new(i).unwrap();
            let err = m.get(42, i).unwrap_err();
            assert!(matches!(err, PageError::PageNotFound(page_id) if page_id == i));

            let page = m.allocate(snapshot).unwrap();
            assert_eq!(page.id(), i);
            assert_eq!(page.contents(), &mut [0; Page::DATA_SIZE]);
            assert_eq!(page.snapshot_id(), snapshot);
            drop(page);
        }

        // Verify pages are in the cache, and are dirty after allocate
        for i in 1..=10 {
            let i = PageId::new(i).unwrap();
            let cached_page = m.page_table.get(&i).expect("page not in cache");
            let dirty_frames = m.dirty_frames.lock();
            assert!(dirty_frames.iter().any(|x| x.0 == cached_page.frame_id && x.1 == i));
        }
    }

    #[test]
    fn test_allocate_get() {
        let snapshot = 1234;
        let f = tempfile::tempfile().expect("temporary file creation failed");
        let opts = BufferPoolManagerOptions::new();
        let m = BufferPoolManager::from_file_with_options(&opts, f.try_clone().unwrap())
            .expect("mmap creation failed");

        for i in 1..=10 {
            let i = PageId::new(i).unwrap();
            let err = m.get(42, i).unwrap_err();
            assert!(matches!(err, PageError::PageNotFound(page_id) if page_id == i));

            let mut page = m.allocate(snapshot).unwrap();
            assert_eq!(page.id(), i);
            assert_eq!(page.contents(), &mut [0; Page::DATA_SIZE]);
            assert_eq!(page.snapshot_id(), snapshot);
            page.contents_mut().iter_mut().for_each(|byte| *byte = 0x12);
            drop(page);

            // Verify the page content with get()
            let page = m.get(snapshot, i).unwrap();
            assert_eq!(page.id(), i);
            assert_eq!(page.contents(), &mut [0x12; Page::DATA_SIZE]);
            assert_eq!(page.snapshot_id(), snapshot);
        }
    }

    #[test]
    fn test_allocate_get_mut() {
        let snapshot = 1235;
        let f = tempfile::tempfile().expect("temporary file creation failed");
        let opts = BufferPoolManagerOptions::new();
        let m = BufferPoolManager::from_file_with_options(&opts, f.try_clone().unwrap())
            .expect("mmap creation failed");

        let mut page = m.allocate(snapshot).unwrap();
        assert_eq!(page.id(), page_id!(1));
        assert_eq!(page.contents(), &mut [0; Page::DATA_SIZE]);
        assert_eq!(page.snapshot_id(), snapshot);
        page.contents_mut().iter_mut().for_each(|byte| *byte = 0xab);
        drop(page);

        let p1 = m.get(snapshot, page_id!(1)).unwrap();
        assert_eq!(p1.id(), page_id!(1));
        assert_eq!(p1.snapshot_id(), snapshot);
        assert_eq!(p1.contents(), &mut [0xab; Page::DATA_SIZE]);

        let p2 = m.allocate(snapshot).unwrap();
        assert_eq!(p2.id(), page_id!(2));
        drop(p2);
        let p3 = m.allocate(snapshot).unwrap();
        assert_eq!(p3.id(), page_id!(3));
        drop(p3);

        let mut p1 = m.get_mut(snapshot, page_id!(1)).unwrap();
        p1.contents_mut().iter_mut().for_each(|byte| *byte = 0xcd);
        drop(p1);

        // Verify the page content with get after get_mut and modify
        let p1 = m.get(snapshot, page_id!(1)).unwrap();
        assert_eq!(p1.id(), page_id!(1));
        assert_eq!(p1.snapshot_id(), snapshot);
        assert_eq!(p1.contents(), &mut [0xcd; Page::DATA_SIZE]);
    }

    #[test]
    fn persistence() {
        let snapshot = 123;
        let temp_file = tempfile::NamedTempFile::new().expect("temporary file creation failed");
        let m = BufferPoolManager::open(temp_file.path()).expect("buffer pool creation failed");
        let f = temp_file.into_file();

        // No page has been allocated; file should be empty
        assert_eq!(len(&f), 0);

        // Allocate a page; verify that the size of the file is `Page::SIZE`
        let mut p = m.allocate(snapshot).expect("page allocation failed");
        p.contents_mut().iter_mut().for_each(|byte| *byte = 0xab);
        drop(p);
        m.sync().expect("sync failed");
        seek(&f, 0);
        assert_eq!(len(&f), 1 * Page::SIZE);
        assert_eq!(read(&f, 8), snapshot.to_le_bytes());
        assert_eq!(read(&f, Page::DATA_SIZE - 8), [0xab; Page::DATA_SIZE - 8]);

        // Repeat the test with more pages
        for i in 1..=255 {
            let mut p = m.allocate(snapshot + i as u64).expect("page allocation failed");
            p.contents_mut().iter_mut().for_each(|byte| *byte = 0xab ^ (i as u8));
        }
        m.sync().expect("sync failed");

        assert_eq!(len(&f), 256 * Page::SIZE);
        for i in 1..=255 {
            seek(&f, i * Page::SIZE as u64);
            assert_eq!(read(&f, 8), (snapshot + i as u64).to_le_bytes());
            assert_eq!(read(&f, Page::DATA_SIZE - 8), [0xab ^ (i as u8); Page::DATA_SIZE - 8]);
        }
    }

    #[test]
    fn get_cache() {
        let snapshot = 123;
        let temp_file = tempfile::NamedTempFile::new().expect("temporary file creation failed");
        {
            let m = BufferPoolManager::open(temp_file.path()).expect("buffer pool creation failed");
            for i in 1..=255 {
                let mut p = m.allocate(snapshot + i as u64).expect("page allocation failed");
                p.contents_mut().iter_mut().for_each(|byte| *byte = 0xab ^ (i as u8));
            }
            m.sync().expect("sync failed");
        }
        {
            // get
            let mut opts = BufferPoolManagerOptions::new();
            opts.page_count(255);
            let m = BufferPoolManager::open_with_options(&opts, temp_file.path())
                .expect("buffer pool creation failed");
            for i in 1..=255 {
                let page_id = PageId::new(i).unwrap();
                let page = m.get(snapshot + i as u64, page_id).expect("page not in cache");
                assert_eq!(page.contents(), &mut [0xab ^ (i as u8); Page::DATA_SIZE]);
                let frame_id = m.page_table.get(&page_id).expect("page not in cache").frame_id;
                let frame = &m.frames[frame_id.0 as usize];
                assert_eq!(frame.ptr as *const u8, page.all_contents().as_ptr());
            }
        }
        {
            // get_mut
            let mut opts = BufferPoolManagerOptions::new();
            opts.page_count(255);
            let m = BufferPoolManager::open_with_options(&opts, temp_file.path())
                .expect("buffer pool creation failed");
            for i in 1..=255 {
                let page_id = PageId::new(i).unwrap();
                let page = m.get_mut(snapshot + i as u64, page_id).expect("page not in cache");
                assert_eq!(page.contents(), &mut [0xab ^ (i as u8); Page::DATA_SIZE]);
                let frame_id = m.page_table.get(&page_id).expect("page not in cache").frame_id;
                let frame = &m.frames[frame_id.0 as usize];
                assert_eq!(frame.ptr as *const u8, page.all_contents().as_ptr());
            }
        }
    }

    #[test]
    fn pool_eviction() {
        let snapshot = 123;
        let temp_file = tempfile::NamedTempFile::new().expect("temporary file creation failed");
        let mut opts = BufferPoolManagerOptions::new();
        let _i = temp_file.path().to_str().unwrap();
        opts.num_frames(10);
        let m = BufferPoolManager::open_with_options(&opts, temp_file.path())
            .expect("buffer pool creation failed");

        (1..=20).for_each(|i| {
            let mut p =
                m.allocate(snapshot + i as u64).expect(&format!("page allocation failed {}", i));
            p.contents_mut().iter_mut().for_each(|byte| *byte = 0x10 + i as u8);
            drop(p);
            if i % 3 == 0 {
                m.sync().expect("sync failed");
            }
        });

        (1..=20).for_each(|i| {
            let page_id = PageId::new(i).unwrap();
            let page =
                m.get(snapshot + i as u64, page_id).expect(&format!("failed to get page {}", i));
            assert_eq!(page.contents(), &mut [0x10 + i as u8; Page::DATA_SIZE]);
        });
    }
}
