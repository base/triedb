use std::{
    ffi::CString,
    fs::File,
    io::{self, IoSlice, Read, Seek, SeekFrom, Write},
    os::fd::FromRawFd,
    path::Path,
    sync::atomic::{AtomicU32, AtomicU64, Ordering},
};

use dashmap::DashMap;
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

#[derive(Debug, Clone, Copy)]
struct FrameId(usize);

#[derive(Debug)]
struct DiskScheduler {}

#[derive(Debug)]
struct LRUReplacer {}

pub struct BufferPoolManagerOptions {
    pub(super) num_frames: usize,
}

impl BufferPoolManagerOptions {
    pub fn new() -> Self {
        Self { num_frames: 1024 * 1024 * 10 }
    }

    pub fn num_frames(&mut self, num_frames: usize) -> &mut Self {
        self.num_frames = num_frames;
        self
    }
}

// TODO: could have a list of dirty pages
#[derive(Debug)]
pub struct BufferPoolManager {
    num_frames: usize,
    page_count: AtomicU32,
    file_len: AtomicU64,
    file: File,
    frames: Vec<Frame>, /* list of frames that hold pages' data, indexed by frame id with fix
                         * num_frames size */
    page_table: DashMap<PageId, FrameHeader>, /* mapping between page id and buffer pool frames,
                                               * indexed by page id with fix num_frames size */
    free_frames: Mutex<Vec<FrameId>>, /* list of free frames that do not hold any pages'
                                       * data, indexed by frame id with fix num_frames
                                       * size */
    dirty_frames: Mutex<Vec<(FrameId, PageId)>>, /* list of dirty frames that need to be flushed
                                                  * to disk,
                                                  * indexed by frame id with fix num_frames size */
    disk_scheduler: DiskScheduler, /* the scheduler to schedule disk flushing operations */
    lru_replacer: LRUReplacer,     /* the replacer to find unpinned/candidate pages for
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

    pub(super) fn open_with_options(
        opts: &BufferPoolManagerOptions,
        path: impl AsRef<Path>,
    ) -> Result<Self, PageError> {
        let path_cstr = CString::new(path.as_ref().to_string_lossy().as_bytes())
            .map_err(|_| PageError::InvalidValue)?;
        let fd = unsafe { libc::open(path_cstr.as_ptr(), libc::O_RDWR | libc::O_CREAT, 0o644) };
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
        let page_count = AtomicU32::new(0);
        let file_len = AtomicU64::new(file.metadata().map_err(PageError::IO)?.len());
        let page_table = DashMap::with_capacity(num_frames);
        let mut frames = Vec::with_capacity(num_frames);
        for _ in 0..num_frames {
            let boxed_array = Box::new([0; Page::SIZE]);
            let ptr = Box::into_raw(boxed_array);
            frames.push(Frame { ptr });
        }
        let dirty_frames = Mutex::new(Vec::with_capacity(num_frames));
        let free_frames = Mutex::new((0..num_frames).map(FrameId).collect::<Vec<_>>());
        let disk_scheduler = DiskScheduler {};
        let lru_replacer = LRUReplacer {};

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
        // TODO: we could run out of free frames, need to evict pages
        free_frames.pop()
    }

    fn grow_if_needed(&self, min_len: u32) -> Result<(), PageError> {
        // TODO: implement this
        Ok(())
    }
}

impl PageManagerTrait for BufferPoolManager {
    /// Retrieves a page from the buffer pool.
    fn get(&self, _snapshot_id: SnapshotId, page_id: PageId) -> Result<Page<'_>, PageError> {
        if page_id > self.page_count.load(Ordering::Relaxed) {
            return Err(PageError::PageNotFound(page_id));
        }
        let cached_page = self.page_table.get(&page_id).map(|frame_header| {
            let frame = &self.frames[frame_header.frame_id.0];
            unsafe { Page::from_ptr(page_id, frame.ptr) }
        });
        if let Some(page) = cached_page {
            return page;
        }

        // Otherwise, we need to load the page from disk
        let mut file = &self.file;
        let frame_id = self.get_free_frame().ok_or(PageError::OutOfMemory)?;

        file.seek(SeekFrom::Start(page_id.as_offset() as u64)).map_err(PageError::IO)?;
        let mut buf = vec![0; Page::SIZE];
        file.read_exact(&mut buf).map_err(PageError::IO)?;
        self.page_table.insert(page_id, FrameHeader { frame_id, pin_count: 0 });
        unsafe { Page::from_ptr(page_id, buf.as_mut_ptr().cast()) }
    }

    /// Retrieves a mutable page from the buffer pool.
    fn get_mut(&self, snapshot_id: SnapshotId, page_id: PageId) -> Result<PageMut<'_>, PageError> {
        if page_id > self.page_count.load(Ordering::Relaxed) {
            return Err(PageError::PageNotFound(page_id));
        }
        let cached_page = self.page_table.get(&page_id).map(|frame_header| {
            let frame = &self.frames[frame_header.frame_id.0];
            unsafe { PageMut::from_ptr(page_id, snapshot_id, frame.ptr) }
        });

        if let Some(page) = cached_page {
            return page;
        }

        // Otherwise, we need to load the page from disk
        let mut file = &self.file;
        let frame_id = self.get_free_frame().ok_or(PageError::OutOfMemory)?;

        file.seek(SeekFrom::Start(page_id.as_offset() as u64)).map_err(PageError::IO)?;
        let mut buf = vec![0; Page::SIZE];
        file.read_exact(&mut buf).map_err(PageError::IO)?;
        self.page_table.insert(page_id, FrameHeader { frame_id, pin_count: 0 });
        self.dirty_frames.lock().push((frame_id, page_id));
        unsafe { PageMut::from_ptr(page_id, snapshot_id, buf.as_mut_ptr().cast()) }
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

        let data = self.frames[frame_id.0].ptr;
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
            let frame = &self.frames[frame_id.0];
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

            let page = m.allocate(snapshot).unwrap();
            assert_eq!(page.id(), i);
            assert_eq!(page.contents(), &mut [0; Page::DATA_SIZE]);
            assert_eq!(page.snapshot_id(), snapshot);
            drop(page);

            let page = m.get(snapshot, i).unwrap();
            assert_eq!(page.id(), i);
            assert_eq!(page.contents(), &mut [0; Page::DATA_SIZE]);
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
            drop(p);
            m.sync().expect("sync failed");
            seek(&f, i * Page::SIZE as u64);
            assert_eq!(len(&f), (i + 1) as usize * Page::SIZE);
            assert_eq!(read(&f, 8), (snapshot + i as u64).to_le_bytes());
            assert_eq!(read(&f, Page::DATA_SIZE - 8), [0xab ^ (i as u8); Page::DATA_SIZE - 8]);
        }
    }
}
