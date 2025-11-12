use crossbeam_channel::{Receiver, Sender};
use fxhash::FxBuildHasher;
use io_uring::{opcode, types, IoUring};
use std::{
    ffi::CString,
    fs::File,
    io::{self, Write},
    os::{
        fd::{AsRawFd, FromRawFd},
        unix::fs::FileExt,
    },
    path::Path,
    sync::{
        atomic::{AtomicU32, AtomicU64, Ordering},
        Arc,
    },
    thread,
};

use dashmap::{DashMap, DashSet};
use parking_lot::{Mutex, RwLock};

use crate::{
    page::{
        manager::cache_evict::CacheEvict,
        state::{PageState, RawPageState},
        Page, PageError, PageId, PageManagerOptions, PageMut,
    },
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

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub(crate) struct FrameId(u32);

pub(crate) type FxMap<K, V> = DashMap<K, V, FxBuildHasher>;
pub(crate) type FxSet<K> = DashSet<K, FxBuildHasher>;

pub struct PageManager {
    num_frames: u32,
    page_count: AtomicU32,
    file: RwLock<File>,
    file_len: AtomicU64,
    frames: Arc<Vec<Frame>>, /* list of frames that hold pages' data, indexed by frame id with
                              * fix num_frames size */
    page_table: FxMap<PageId, FrameId>, /* mapping between page id and buffer pool frames,
                                         * indexed by page id with fix num_frames size */
    original_free_frame_idx: AtomicU32,
    lru_replacer: Arc<CacheEvict>, /* the replacer to find unpinned/candidate pages for eviction */
    loading_page: FxSet<PageId>,   /* set of pages that are being loaded from disk */

    io_uring: Arc<RwLock<IoUring>>,
    tx_job: Sender<WriteMessage>,
    drop_pages: Mutex<Vec<PageId>>,
}

enum WriteMessage {
    Pages(Vec<(PageId, FrameId)>),
    #[allow(dead_code)]
    Shutdown,
}

impl std::fmt::Debug for PageManager {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PageManager")
            .field("num_frames", &self.num_frames)
            .field("page_count", &self.page_count)
            .field("file", &self.file)
            .field("file_len", &self.file_len)
            .field("frames", &self.frames)
            .field("page_table", &self.page_table)
            .field("original_free_frame_idx", &self.original_free_frame_idx)
            .field("lru_replacer", &self.lru_replacer)
            .field("loading_page", &self.loading_page)
            .field("io_uring", &"<IoUring>")
            .finish()
    }
}

impl PageManager {
    pub fn options() -> PageManagerOptions {
        PageManagerOptions::new()
    }

    pub fn open(path: impl AsRef<Path>) -> Result<Self, PageError> {
        let opts = PageManagerOptions::new();
        Self::open_with_options(&opts, path)
    }

    pub fn open_with_options(
        opts: &PageManagerOptions,
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
        opts: &PageManagerOptions,
        file: File,
    ) -> Result<Self, PageError> {
        let num_frames = opts.num_frames;
        let page_count = AtomicU32::new(opts.page_count);
        let file_len = AtomicU64::new(file.metadata().map_err(PageError::IO)?.len());
        let page_table =
            DashMap::with_capacity_and_hasher(num_frames as usize, FxBuildHasher::default());
        let mut frames = Vec::with_capacity(num_frames as usize);
        for _ in 0..num_frames {
            let boxed_array = Box::new([0; Page::SIZE]);
            let ptr = Box::into_raw(boxed_array);
            frames.push(Frame { ptr });
        }
        let lru_replacer = Arc::new(CacheEvict::new(num_frames as usize));
        let loading_page =
            DashSet::with_capacity_and_hasher(num_frames as usize, FxBuildHasher::default());

        // Initialize io_uring with queue depth base on num_frames
        let queue_depth = num_frames.min(2048) as u32;
        let io_uring = IoUring::new(queue_depth)
            .map_err(|e| PageError::IO(io::Error::new(io::ErrorKind::Other, e)))?;

        let (tx_job, rx_job) = crossbeam_channel::unbounded();
        let page_manager = PageManager {
            num_frames,
            page_count,
            file: RwLock::new(file),
            file_len,
            frames: Arc::new(frames),
            page_table,
            original_free_frame_idx: AtomicU32::new(0),
            lru_replacer,
            loading_page,

            io_uring: Arc::new(RwLock::new(io_uring)),
            tx_job,
            drop_pages: Mutex::new(Vec::new()),
        };

        page_manager.start_write_worker(rx_job)?;

        Ok(page_manager)
    }

    fn start_write_worker(&self, rx_job: Receiver<WriteMessage>) -> Result<(), PageError> {
        let worker_file = self.file.write().try_clone().map_err(PageError::IO)?;
        let frames = self.frames.clone();
        let io_uring = self.io_uring.clone();
        let lru_replacer = self.lru_replacer.clone();
        thread::spawn(move || {
            loop {
                match rx_job.recv() {
                    Ok(WriteMessage::Pages(pages)) => {
                        let result = Self::write_updated_pages(
                            io_uring.clone(),
                            frames.clone(),
                            &pages,
                            worker_file.try_clone().unwrap(),
                        );
                        // TODO: need to handle error here
                        if result.is_err() {
                            panic!("{:?}", result);
                        }
                        // Note: it's possible that when a mut page get dropped, before it's wrote
                        // to the disk, the same page is used again as mut page.  If the page_id is
                        // removed from update_frames while its data is being updated, we will lost
                        // the data. Thought in the current schema doesn't allow this, any further
                        // change needs to consider this.
                        pages.iter().for_each(|(page_id, _)| {
                            lru_replacer.update_frames.remove(page_id);
                        });
                    }
                    Ok(WriteMessage::Shutdown) => {
                        println!("Shutdown");
                        // ignore for now
                    }
                    Err(_) => {
                        // Channel closed
                        break;
                    }
                }
            }
        });
        Ok(())
    }

    fn write_updated_pages(
        ring: Arc<RwLock<IoUring>>,
        frames: Arc<Vec<Frame>>,
        pages: &[(PageId, FrameId)],
        file: File,
    ) -> io::Result<()> {
        // println!("Write updated pages: {:?}", pages.len());
        let fd = file.as_raw_fd();
        let mut op_count = 0;
        let mut ring_guard = ring.write();

        for page in pages {
            let page_id = page.0;
            let frame_id = page.1;
            let offset = page_id.as_offset();
            let frame = &frames[frame_id.0 as usize];
            let page_data =
                unsafe { std::slice::from_raw_parts(frame.ptr as *const u8, Page::SIZE) };

            // Create write operation
            let write_op = opcode::Write::new(types::Fd(fd), page_data.as_ptr(), Page::SIZE as u32)
                .offset(offset as u64)
                .build()
                .user_data(op_count);
            // Submit to ring
            loop {
                let mut sq = ring_guard.submission();
                match unsafe { sq.push(&write_op) } {
                    Ok(_) => {
                        op_count += 1;
                        drop(sq);
                        break;
                    }
                    Err(_) => {
                        // Submission queue is full, submit and wait
                        drop(sq);
                        let _ = ring_guard.submit_and_wait(1);
                    }
                }
            }
        }
        // Submit all pending operations
        let _ = ring_guard.submit();

        // Wait for jobs to complete
        let mut completed = 0;
        while completed < op_count {
            let cq = ring_guard.completion();
            for cqe in cq {
                let result = cqe.result();
                if result < 0 {
                    return Err(io::Error::from_raw_os_error(-result));
                }
                completed += 1;
            }
            if completed < op_count {
                ring_guard.submit_and_wait(1)?;
            }
        }
        Ok(())
    }

    #[cfg(test)]
    pub fn open_temp_file() -> Result<Self, PageError> {
        Self::options().open_temp_file()
    }

    /// Retrieves a page from the buffer pool.
    pub fn get(&self, page_id: PageId) -> Result<Page<'_>, PageError> {
        if page_id > self.page_count.load(Ordering::Relaxed) {
            return Err(PageError::PageNotFound(page_id));
        }
        loop {
            // Check if page is already in the cache
            if let Some(frame_id) = self.page_table.get(&page_id) {
                let frame = &self.frames[frame_id.0 as usize];
                self.lru_replacer.touch(page_id).map_err(|_| PageError::EvictionPolicy)?;
                return unsafe { Page::from_ptr(page_id, frame.ptr, self) };
            }

            // Otherwise, need to load the page from disk
            if self.loading_page.insert(page_id) {
                // This thread is the first to load this page
                let frame_id = self.get_free_frame().ok_or(PageError::OutOfMemory)?;
                let buf: *mut [u8; Page::SIZE] = self.frames[frame_id.0 as usize].ptr;
                unsafe {
                    self.file
                        .read()
                        .read_exact_at(&mut *buf, page_id.as_offset() as u64)
                        .map_err(PageError::IO)?;
                }
                self.page_table.insert(page_id, frame_id);
                self.lru_replacer.pin_read(page_id).map_err(|_| PageError::EvictionPolicy)?;
                self.loading_page.remove(&page_id);
                return unsafe { Page::from_ptr(page_id, buf, self) };
            }
            // Another thread is already loading this page, spin/yield and retry
            std::thread::yield_now();
        }
    }

    /// Retrieves a mutable page from the buffer pool.
    pub fn get_mut(
        &self,
        snapshot_id: SnapshotId,
        page_id: PageId,
    ) -> Result<PageMut<'_>, PageError> {
        if page_id > self.page_count.load(Ordering::Relaxed) {
            return Err(PageError::PageNotFound(page_id));
        }
        loop {
            // Check if page is already in the cache
            if let Some(frame_id) = self.page_table.get(&page_id) {
                self.lru_replacer
                    .pin_write_update_page(*frame_id, page_id)
                    .map_err(|_| PageError::EvictionPolicy)?;
                let frame = &self.frames[frame_id.0 as usize];
                return unsafe { PageMut::from_ptr(page_id, snapshot_id, frame.ptr, self) };
            }
            // Otherwise, need to load the page from disk
            if self.loading_page.insert(page_id) {
                // This thread is the first to load this page
                let frame_id = self.get_free_frame().ok_or(PageError::OutOfMemory)?;
                let buf: *mut [u8; Page::SIZE] = self.frames[frame_id.0 as usize].ptr;
                unsafe {
                    self.file
                        .read()
                        .read_exact_at(&mut *buf, page_id.as_offset() as u64)
                        .map_err(PageError::IO)?;
                }
                self.page_table.insert(page_id, frame_id);
                self.lru_replacer
                    .pin_write_update_page(frame_id, page_id)
                    .map_err(|_| PageError::EvictionPolicy)?;
                self.loading_page.remove(&page_id);
                return unsafe { PageMut::from_ptr(page_id, snapshot_id, buf, self) };
            } else {
                // Another thread is already loading this page, spin/yield and retry
                std::thread::yield_now();
                continue;
            }
        }
    }

    /// Adds a new page to the buffer pool.
    ///
    /// Returns an error if the buffer pool is full.
    pub fn allocate(&self, snapshot_id: SnapshotId) -> Result<PageMut<'_>, PageError> {
        let frame_id = self.get_free_frame().ok_or(PageError::OutOfMemory)?;
        let (page_id, new_count) = self.next_page_id().ok_or(PageError::PageLimitReached)?;

        self.grow_if_needed(new_count as u64 * Page::SIZE as u64)?;

        self.page_table.insert(page_id, frame_id);
        self.lru_replacer
            .pin_write_new_page(frame_id, page_id)
            .map_err(|_| PageError::EvictionPolicy)?;

        let data = self.frames[frame_id.0 as usize].ptr;
        unsafe { PageMut::acquire_unchecked(page_id, snapshot_id, data, self) }
    }

    /// Checks if a page is currently in the Dirty state.
    ///
    /// This method allows checking if a page is being written to without
    /// the overhead of acquiring the page.
    pub fn is_dirty(&self, page_id: PageId) -> Result<bool, PageError> {
        if page_id > self.page_count.load(Ordering::Relaxed) {
            return Err(PageError::PageNotFound(page_id));
        }
        // A page is dirty if it is in the page_table
        if let Some(frame_id) = self.page_table.get(&page_id) {
            let frame = &self.frames[frame_id.0 as usize];
            // SAFETY: We're just reading the state atomically, respecting the memory model
            let state = unsafe { RawPageState::from_ptr(frame.ptr.cast()) };

            Ok(matches!(state.load(), PageState::Dirty(_)))
        } else {
            // Otherwise, the page is not dirty
            Ok(false)
        }
    }

    /// Syncs the buffer pool to the file.
    ///
    /// New pages at the end of the file are batch written using vectored I/O Writev, since they are
    /// guaranteed to be contiguous. Update pages are usually random pages scattered throughout
    /// the file, and written individually with Write.
    pub fn sync(&self) -> io::Result<()> {
        let file = self.file.read();
        let fd = file.as_raw_fd();

        let mut new_pages = self.lru_replacer.new_frames.lock();
        if new_pages.is_empty() && self.lru_replacer.update_frames.is_empty() {
            return Ok(());
        }

        // Submit writes to io_uring
        let mut ring_guard = self.io_uring.write();
        let mut op_count = 0;

        // Write contiguous new pages as a batch using writev.
        // Note: iovecs must stay alive until operations complete, so we define it outside the scope
        let _iovecs = if !new_pages.is_empty() {
            // Collect iovec for new pages
            let iovecs: Vec<libc::iovec> = new_pages
                .iter()
                .map(|(frame_id, _)| {
                    let frame = &self.frames[frame_id.0 as usize];
                    libc::iovec { iov_base: frame.ptr as *mut libc::c_void, iov_len: Page::SIZE }
                })
                .collect();

            // Get the offset of the first new page
            let first_offset = new_pages[0].1.as_offset() as u64;

            unsafe {
                let writev_op =
                    opcode::Writev::new(types::Fd(fd), iovecs.as_ptr(), iovecs.len() as u32)
                        .offset(first_offset)
                        .build()
                        .user_data(op_count);

                // Submit to ring
                loop {
                    let mut sq = ring_guard.submission();
                    match sq.push(&writev_op) {
                        Ok(_) => {
                            op_count += 1;
                            break;
                        }
                        Err(_) => {
                            // Submission queue is full, submit and wait
                            drop(sq);
                            ring_guard.submit_and_wait(1)?;
                        }
                    }
                }
            }

            Some(iovecs)
        } else {
            None
        };

        // Write update_pages individually (they may not be contiguous)
        for entry in self.lru_replacer.update_frames.iter() {
            let frame_id = *entry.value();
            let page_id = *entry.key();
            let frame = &self.frames[frame_id.0 as usize];
            let offset = page_id.as_offset();

            let page_data =
                unsafe { std::slice::from_raw_parts(frame.ptr as *const u8, Page::SIZE) };
            // Create write operation
            let write_op = opcode::Write::new(types::Fd(fd), page_data.as_ptr(), Page::SIZE as u32)
                .offset(offset as u64)
                .build()
                .user_data(op_count);
            // Submit to ring
            loop {
                let mut sq = ring_guard.submission();
                match unsafe { sq.push(&write_op) } {
                    Ok(_) => {
                        op_count += 1;
                        break;
                    }
                    Err(_) => {
                        // Submission queue is full, submit and wait
                        drop(sq);
                        ring_guard.submit_and_wait(1)?;
                    }
                }
            }
        }

        // Submit all pending operations
        ring_guard.submit()?;

        // Do cleanup work
        // println!("sync");
        // println!("\tdrop_pages: {:?}", self.lru_replacer.drop_pages.len());
        // println!("\tupdate_pages: {:?}", self.lru_replacer.update_frames.len());
        // println!("\tnew_pages: {:?}", new_pages.len());

        new_pages.iter().for_each(|(_, page_id)| self.lru_replacer.unpin(*page_id).unwrap());
        new_pages.clear();
        // TODO: is there any race condition here?
        self.lru_replacer
            .update_frames
            .iter()
            .for_each(|entry| self.lru_replacer.unpin(*entry.key()).unwrap());
        self.lru_replacer.update_frames.clear();
        self.drop_pages.lock().clear();

        // Wait for all jobs to complete
        let mut completed = 0;
        while completed < op_count {
            let cq = ring_guard.completion();
            for cqe in cq {
                let result = cqe.result();
                if result < 0 {
                    return Err(io::Error::from_raw_os_error(-result));
                }
                completed += 1;
            }
            if completed < op_count {
                ring_guard.submit_and_wait(1)?;
            }
        }

        // Drop the write lock on io_uring before calling file operations
        drop(ring_guard);
        drop(file);

        // println!("sync, new_pages: {:?}", new_pages);
        // println!("sync, update_pages: {:?}", update_pages);
        self.file.write().flush()?;

        Ok(())
    }

    /// Syncs and closes the buffer pool.
    pub fn close(&self) -> io::Result<()> {
        self.sync()
    }

    /// Returns the number of pages currently stored in the file.
    #[inline]
    pub fn size(&self) -> u32 {
        self.page_count.load(Ordering::Relaxed)
    }

    #[inline]
    pub fn capacity(&self) -> u32 {
        self.num_frames
    }

    #[inline]
    pub fn drop_page(&self, page_id: PageId) {
        self.lru_replacer.unpin(page_id).unwrap();
    }

    #[inline]
    pub fn drop_page_mut(&self, page_id: PageId) {
        if self.lru_replacer.update_frames.get(&page_id).is_some() {
            let mut drop_pages = self.drop_pages.lock();
            drop_pages.push(page_id);
            if drop_pages.len() >= 10 {
                // iter thru all items in drop_pages and remove from the drop_pages
                let mut pages = Vec::with_capacity(10);
                drop_pages.iter().for_each(|p| {
                    if let Some(f) = self.page_table.get(p) {
                        pages.push((*f.key(), *f.value()));
                    }
                });
                self.tx_job.send(WriteMessage::Pages(pages)).unwrap();
                drop_pages.clear();
            }
        }
    }

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
                Err(val) => old_count = val, // Another thread modiled page_count, retry.
            }
        }
    }

    fn get_free_frame(&self) -> Option<FrameId> {
        let mut original_free_frame_idx = self.original_free_frame_idx.load(Ordering::Relaxed);
        loop {
            if original_free_frame_idx < self.num_frames {
                match self.original_free_frame_idx.compare_exchange_weak(
                    original_free_frame_idx,
                    original_free_frame_idx + 1,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return Some(FrameId(original_free_frame_idx)),
                    Err(val) => original_free_frame_idx = val, /* Another thread modified original_free_frame_idx, retry. */
                }
            } else {
                let evicted_page = self.lru_replacer.evict();
                if let Some(page_id) = evicted_page {
                    return self.page_table.remove(&page_id).map(|(_, frame_id)| frame_id);
                } else {
                    return None;
                }
            }
        }
    }

    #[inline]
    fn grow_if_needed(&self, min_len: u64) -> Result<(), PageError> {
        if min_len <= self.file_len.load(Ordering::Relaxed) {
            return Ok(());
        }
        // Acquire write lock to grow the file
        let file = &mut self.file.write();
        let cur_len = self.file_len.load(Ordering::Relaxed);
        if min_len <= cur_len {
            return Ok(());
        }
        // Grow the file by at least 12.5% of current size, or 4MiB, whichever is larger
        let increment = (cur_len / 8).max(1024 * Page::SIZE as u64);
        file.set_len(cur_len + increment).map_err(PageError::IO)?;
        self.file_len.store(cur_len + increment, Ordering::Relaxed);
        Ok(())
    }
}

impl Drop for PageManager {
    fn drop(&mut self) {
        // Sync the remaining work
        if let Err(e) = self.sync() {
            eprintln!("Warning: Sync failed during drop: {}", e);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::page_id;
    use std::io::SeekFrom;

    use super::*;
    use std::{
        io::Seek,
        sync::{Arc, Barrier},
        thread,
    };

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
    fn test_is_dirty() {
        let snapshot = 1234;
        let f = tempfile::tempfile().expect("temporary file creation failed");
        let mut opts = PageManagerOptions::new();
        opts.num_frames(255);
        let m = PageManager::from_file_with_options(&opts, f.try_clone().unwrap())
            .expect("mmap creation failed");

        let mut page = m.allocate(snapshot).unwrap();
        page.contents_mut().iter_mut().for_each(|byte| *byte = 0x12);
        assert!(m.is_dirty(page_id!(1)).unwrap());
        drop(page);
        assert!(!m.is_dirty(page_id!(1)).unwrap());
        m.sync().expect("sync failed");
        assert!(!m.is_dirty(page_id!(1)).unwrap());
    }

    #[test]
    fn test_allocate_cache() {
        let snapshot = 1234;
        let f = tempfile::tempfile().expect("temporary file creation failed");
        let mut opts = PageManagerOptions::new();
        opts.num_frames(255);
        let m = PageManager::from_file_with_options(&opts, f.try_clone().unwrap())
            .expect("mmap creation failed");

        for i in 1..=10 {
            let i = PageId::new(i).unwrap();
            let err = m.get(i).unwrap_err();
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
            let frame_id = m.page_table.get(&i).expect("page not in cache");
            let dirty_frames = m.lru_replacer.new_frames.lock();
            assert!(dirty_frames.iter().any(|x| x.0 == *frame_id && x.1 == i));
        }
    }

    #[test]
    fn test_allocate_get() {
        let snapshot = 1234;
        let f = tempfile::tempfile().expect("temporary file creation failed");
        let mut opts = PageManagerOptions::new();
        opts.num_frames(255);
        let m = PageManager::from_file_with_options(&opts, f.try_clone().unwrap())
            .expect("mmap creation failed");

        for i in 1..=10 {
            let i = PageId::new(i).unwrap();
            let err = m.get(i).unwrap_err();
            assert!(matches!(err, PageError::PageNotFound(page_id) if page_id == i));

            let mut page = m.allocate(snapshot).unwrap();
            assert_eq!(page.id(), i);
            assert_eq!(page.contents(), &mut [0; Page::DATA_SIZE]);
            assert_eq!(page.snapshot_id(), snapshot);
            page.contents_mut().iter_mut().for_each(|byte| *byte = 0x12);
            drop(page);

            // Verify the page content with get()
            let page = m.get(i).unwrap();
            assert_eq!(page.id(), i);
            assert_eq!(page.contents(), &mut [0x12; Page::DATA_SIZE]);
            assert_eq!(page.snapshot_id(), snapshot);
        }

        // Verify the capability of frame
    }

    #[test]
    fn test_allocate_get_mut() {
        let snapshot = 1235;
        let f = tempfile::tempfile().expect("temporary file creation failed");
        let mut opts = PageManagerOptions::new();
        opts.num_frames(255);
        let m = PageManager::from_file_with_options(&opts, f.try_clone().unwrap())
            .expect("mmap creation failed");

        let mut page = m.allocate(snapshot).unwrap();
        assert_eq!(page.id(), page_id!(1));
        assert_eq!(page.contents(), &mut [0; Page::DATA_SIZE]);
        assert_eq!(page.snapshot_id(), snapshot);
        page.contents_mut().iter_mut().for_each(|byte| *byte = 0xab);
        drop(page);

        let p1 = m.get(page_id!(1)).unwrap();
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
        let p1 = m.get(page_id!(1)).unwrap();
        assert_eq!(p1.id(), page_id!(1));
        assert_eq!(p1.snapshot_id(), snapshot);
        assert_eq!(p1.contents(), &mut [0xcd; Page::DATA_SIZE]);
    }

    #[test]
    fn persistence() {
        let snapshot = 123;
        let f = tempfile::tempfile().expect("temporary file creation failed");
        let mut opts = PageManagerOptions::new();
        opts.num_frames(255);
        let m = PageManager::from_file_with_options(&opts, f.try_clone().unwrap())
            .expect("buffer pool creation failed");

        // No page has been allocated; file should be empty
        assert_eq!(len(&f), 0);

        // Allocate a page; verify that the size of the file is `1024 * Page::SIZE`
        let mut p = m.allocate(snapshot).expect("page allocation failed");
        p.contents_mut().iter_mut().for_each(|byte| *byte = 0xab);
        drop(p);
        m.sync().expect("sync failed");
        seek(&f, 0);
        assert_eq!(len(&f), 1024 * Page::SIZE);
        assert_eq!(read(&f, 8), snapshot.to_le_bytes());
        assert_eq!(read(&f, Page::DATA_SIZE - 8), [0xab; Page::DATA_SIZE - 8]);

        // Repeat the test with more pages
        for i in 1..=255 {
            let mut p = m.allocate(snapshot + i as u64).expect("page allocation failed");
            p.contents_mut().iter_mut().for_each(|byte| *byte = 0xab ^ (i as u8));
        }
        m.sync().expect("sync failed");

        assert_eq!(len(&f), 1024 * Page::SIZE);
        for i in 1..=255 {
            seek(&f, i * Page::SIZE as u64);
            assert_eq!(read(&f, 8), (snapshot + i).to_le_bytes());
            assert_eq!(read(&f, Page::DATA_SIZE - 8), [0xab ^ (i as u8); Page::DATA_SIZE - 8]);
        }
    }

    #[test]
    fn get_cache() {
        let snapshot = 123;
        let f = tempfile::tempfile().expect("temporary file creation failed");
        {
            let mut opts = PageManagerOptions::new();
            opts.num_frames(255);
            let m = PageManager::from_file_with_options(&opts, f.try_clone().unwrap())
                .expect("buffer pool creation failed");
            for i in 1..=255 {
                let mut p = m.allocate(snapshot + i as u64).expect("page allocation failed");
                p.contents_mut().iter_mut().for_each(|byte| *byte = 0xab ^ (i as u8));
            }
            m.sync().expect("sync failed");
        }
        {
            // get
            let mut opts = PageManagerOptions::new();
            opts.num_frames(255).page_count(255);
            let m = PageManager::from_file_with_options(&opts, f.try_clone().unwrap())
                .expect("buffer pool creation failed");
            for i in 1..=255 {
                let page_id = PageId::new(i).unwrap();
                let page = m.get(page_id).expect("page not in cache");
                assert_eq!(page.contents(), &mut [0xab ^ (i as u8); Page::DATA_SIZE]);
                let frame_id = m.page_table.get(&page_id).expect("page not in cache");
                let frame = &m.frames[frame_id.0 as usize];
                assert_eq!(frame.ptr as *const u8, page.all_contents().as_ptr());
            }
        }
        {
            // get_mut
            let mut opts = PageManagerOptions::new();
            opts.num_frames(255).page_count(255);
            let m = PageManager::from_file_with_options(&opts, f.try_clone().unwrap())
                .expect("buffer pool creation failed");
            for i in 1..=255 {
                let page_id = PageId::new(i).unwrap();
                let page = m.get_mut(snapshot + i as u64, page_id).expect("page not in cache");
                assert_eq!(page.contents(), &mut [0xab ^ (i as u8); Page::DATA_SIZE]);
                let frame_id = m.page_table.get(&page_id).expect("page not in cache");
                let frame = &m.frames[frame_id.0 as usize];
                assert_eq!(frame.ptr as *const u8, page.all_contents().as_ptr());
            }
        }
    }

    #[test]
    fn test_allocate_oom() {
        let snapshot = 1234;
        let f = tempfile::tempfile().expect("temporary file creation failed");
        let mut opts = PageManagerOptions::new();
        opts.num_frames(10);
        let m = PageManager::from_file_with_options(&opts, f.try_clone().unwrap())
            .expect("mmap creation failed");

        for _ in 1..=10 {
            m.allocate(snapshot).expect("failed to allocate page");
        }
        let page = m.allocate(snapshot).unwrap_err();
        assert!(matches!(page, PageError::OutOfMemory));
    }

    #[test]
    fn pool_eviction() {
        let snapshot = 123;
        let temp_file = tempfile::NamedTempFile::new().expect("temporary file creation failed");
        {
            let mut opts = PageManagerOptions::new();
            opts.num_frames(200);
            let m = PageManager::open_with_options(&opts, temp_file.path())
                .expect("buffer pool creation failed");

            (1..=200).for_each(|i| {
                let mut p = m
                    .allocate(snapshot + i as u64)
                    .unwrap_or_else(|_| panic!("page allocation failed {i}"));
                p.contents_mut().iter_mut().for_each(|byte| *byte = 0x10 + i as u8);
            });
            m.sync().expect("sync failed");
        }
        {
            let mut opts = PageManagerOptions::new();
            opts.num_frames(10).page_count(200);
            let m = PageManager::open_with_options(&opts, temp_file.path())
                .expect("buffer pool creation failed");
            (1..=200).for_each(|i| {
                let page_id = PageId::new(i).unwrap();
                let page = m.get(page_id).unwrap_or_else(|_| panic!("failed to get page {i}"));
                assert_eq!(page.contents(), &mut [0x10 + i as u8; Page::DATA_SIZE]);
            });
        }
    }

    #[test]
    fn test_concurrent_get_same_page() {
        // Test high contention race by having multiple threads accessing same pages with cache
        // hits/misses
        let snapshot = 1234;
        let temp_file = tempfile::NamedTempFile::new().expect("temporary file creation failed");
        let total_pages = 50;
        let num_frames = 200; // Plenty of frames to avoid eviction

        // Pre-populate the file with test data
        {
            let mut opts = PageManagerOptions::new();
            opts.num_frames(num_frames);
            let m = PageManager::open_with_options(&opts, temp_file.path())
                .expect("buffer pool creation failed");

            // Allocate and initialize test pages
            for i in 1..=total_pages {
                let mut page = m.allocate(snapshot + i as u64).expect("page allocation failed");
                page.contents_mut().iter_mut().for_each(|byte| *byte = i as u8);
                drop(page);
            }
            m.sync().expect("sync failed");
        }

        // Test concurrent access to the same pages
        {
            let mut opts = PageManagerOptions::new();
            opts.num_frames(num_frames).page_count(total_pages);
            let m = Arc::new(
                PageManager::open_with_options(&opts, temp_file.path())
                    .expect("buffer pool creation failed"),
            );

            let num_threads = 16;
            let iterations = 100;
            let barrier = Arc::new(Barrier::new(num_threads));

            let handles: Vec<_> = (0..num_threads)
                .map(|thread_id| {
                    let m = m.clone();
                    let barrier = barrier.clone();

                    thread::spawn(move || {
                        barrier.wait(); // Synchronize start to maximize race conditions

                        for iter in 0..iterations {
                            // Mix of different pages, but with high probability of conflicts
                            let page_id =
                                PageId::new(1 + (iter as u32 + thread_id as u32) % 10).unwrap();

                            match m.get(page_id) {
                                Ok(page) => {
                                    // Verify page contents are correct
                                    let expected = page_id.as_u32() as u8;
                                    assert_eq!(page.contents(), &[expected; Page::DATA_SIZE]);

                                    // Hold the page for a random short time to increase contention
                                    if (thread_id + iter) % 7 == 0 {
                                        thread::sleep(std::time::Duration::from_micros(1));
                                    }
                                }
                                Err(e) => {
                                    panic!("Unexpected error getting page {page_id}: {e:?}")
                                }
                            }
                        }
                    })
                })
                .collect();

            for handle in handles {
                handle.join().expect("thread panicked");
            }

            // Verify final state consistency
            for i in 1..=total_pages {
                let page_id = PageId::new(i).unwrap();
                let page = m.get(page_id).expect("page should exist");
                assert_eq!(page.contents(), &[i as u8; Page::DATA_SIZE]);
            }
        }
    }

    #[test]
    fn test_concurrent_get_different_pages_limited_frames() {
        // Test eviction under pressure race condition
        let snapshot = 1234;
        let temp_file = tempfile::NamedTempFile::new().expect("temporary file creation failed");
        let total_pages = 1000;

        // Pre-populate the file with test data
        {
            let mut opts = PageManagerOptions::new();
            opts.num_frames(1000);
            let m = PageManager::open_with_options(&opts, temp_file.path())
                .expect("buffer pool creation failed");

            for i in 1..=total_pages {
                let mut page = m.allocate(snapshot + i as u64).expect("page allocation failed");
                page.contents_mut().iter_mut().for_each(|byte| *byte = i as u8);
                drop(page);
            }
            m.sync().expect("sync failed");
        }

        // Test with limited frames to force eviction
        {
            let num_threads = 16;
            let iterations = 50;
            let num_frames = 32;
            let mut opts = PageManagerOptions::new();
            opts.num_frames(num_frames).page_count(total_pages); // Force frequent eviction
            let m = Arc::new(
                PageManager::open_with_options(&opts, temp_file.path())
                    .expect("buffer pool creation failed"),
            );

            let barrier = Arc::new(Barrier::new(num_threads));

            let handles: Vec<_> = (0..num_threads)
                .map(|thread_id| {
                    let m = m.clone();
                    let barrier = barrier.clone();

                    thread::spawn(move || {
                        barrier.wait();

                        for iter in 0..iterations {
                            // Access different pages to force frame reuse
                            let page_id = PageId::new(
                                1 + (thread_id as u32 * iterations + iter) % total_pages,
                            )
                            .unwrap();

                            match m.get(page_id) {
                                Ok(page) => {
                                    let expected = page_id.as_u32() as u8;
                                    assert_eq!(page.contents(), &[expected; Page::DATA_SIZE]);
                                }
                                Err(e) => {
                                    panic!("Unexpected error getting page {page_id}: {e:?}")
                                }
                            }
                        }
                    })
                })
                .collect();

            for handle in handles {
                handle.join().expect("thread panicked");
            }
        }
    }

    #[test]
    fn test_concurrent_allocate_and_get() {
        // Test allocation vs get race condition
        let snapshot = 1234;
        let temp_file = tempfile::NamedTempFile::new().expect("temporary file creation failed");
        let num_threads = 8;
        let pages_per_thread: usize = 64;
        let mut opts = PageManagerOptions::new();
        opts.num_frames(pages_per_thread as u32 + 1);
        let m = Arc::new(
            PageManager::open_with_options(&opts, temp_file.path())
                .expect("buffer pool creation failed"),
        );
        let barrier = Arc::new(Barrier::new(num_threads));

        let handles: Vec<_> = (0..num_threads)
            .map(|thread_id| {
                let m = m.clone();
                let barrier = barrier.clone();

                thread::spawn(move || {
                    barrier.wait();

                    if thread_id == 0 {
                        // Allocate new pages
                        for i in 0..pages_per_thread {
                            match m.allocate(snapshot + thread_id as u64 * 1000 + i as u64) {
                                Ok(mut page) => {
                                    page.contents_mut().iter_mut().for_each(|byte| {
                                        *byte = (thread_id as u8).wrapping_add(i as u8)
                                    });
                                }
                                Err(e) => panic!("Unexpected error allocating page: {e:?}"),
                            }
                        }
                    } else {
                        for i in 0..pages_per_thread {
                            // Try to get existing pages
                            let page_id =
                                PageId::new(1 + (thread_id as u32 + i as u32) % 20).unwrap();
                            match m.get(page_id) {
                                Ok(_page) => {
                                    // Expected
                                }
                                Err(PageError::PageNotFound(_)) => {
                                    // Expected if page doesn't exist yet
                                }
                                Err(PageError::PageDirty(_)) => {
                                    // Expected if page is dirty
                                }
                                Err(e) => {
                                    panic!("Unexpected error getting page {page_id}: {e:?}")
                                }
                            }
                        }
                    }
                })
            })
            .collect();

        for handle in handles {
            handle.join().expect("thread panicked");
        }
    }
}
