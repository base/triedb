use crate::{
    executor::threadpool,
    page::{Page, PageId},
};
use memmap2::MmapRaw;
use parking_lot::{Condvar, Mutex, MutexGuard};
use rayon::{ThreadPool, ThreadPoolBuildError};
use std::{
    collections::BTreeSet,
    num::NonZero,
    sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        Arc,
    },
};

const MAX_PAGE_COUNT: u32 = 64;

/// Writes pages to secondary storage using parallel I/O in background threads.
#[derive(Debug)]
pub(in crate::page) struct PageSyncer {
    thread_pool: ThreadPool,
    inner: Arc<PageSyncerInner>,
}

#[derive(Debug)]
struct PageSyncerInner {
    pub(super) mmap: MmapRaw,
    /// Set of pages that are "dirty" (have been modified in-memory) and should be synced to
    /// secondary storage.
    dirty_pages: Mutex<BTreeSet<PageId>>,
    /// Condition set whenever a new page is added to `dirty_pages`. Used to notify writer threads.
    new_dirty_page: Condvar,
    /// Condition set whenever `dirty_pages` is emptied out. Used to notify `sync()`.
    dirty_pages_consumed: Condvar,
    /// Set to `true` when `PageSyncer` is dropped, to signal all threads to quit.
    quit: AtomicBool,
    /// Tracks the number of active threads. Used by `stop_threads()` to know when to return.
    active_threads: AtomicUsize,
}

impl PageSyncer {
    pub(super) fn new(
        mmap: MmapRaw,
        num_threads: NonZero<usize>,
    ) -> Result<Self, ThreadPoolBuildError> {
        let thread_pool = threadpool::builder().num_threads(num_threads.get()).build()?;
        let syncer = Self {
            thread_pool,
            inner: Arc::new(PageSyncerInner {
                mmap,
                dirty_pages: Mutex::new(BTreeSet::new()),
                new_dirty_page: Condvar::new(),
                dirty_pages_consumed: Condvar::new(),
                quit: AtomicBool::new(false),
                active_threads: AtomicUsize::new(0),
            }),
        };
        syncer.spawn_threads();
        Ok(syncer)
    }

    #[must_use]
    pub(super) fn mmap(&self) -> &MmapRaw {
        &self.inner.mmap
    }

    pub(in crate::page) fn mark_dirty(&self, page_id: PageId) {
        let mut dirty_pages = self.inner.dirty_pages.lock();
        if dirty_pages.insert(page_id) {
            self.inner.new_dirty_page.notify_one();
        }
    }

    pub(super) fn sync(&self) {
        let mut dirty_pages = self.inner.dirty_pages.lock();
        if !dirty_pages.is_empty() {
            // Wait once for the writer threads to consume `dirty_pages`. It's possible that right
            // after that happens, another worker thread adds pages to `dirty_pages`, but we don't
            // care: here we want to flush out all the pages that were in the set at the time that
            // `sync()` was called; if more pages get added later, it's not our responsibility to
            // wait for those to be synced.
            //
            // The problem with waiting until `dirty_pages` is really empty (i.e. changing the `if`
            // to a `while`) is that this method would *potentially* be blocked forever.
            self.inner.dirty_pages_consumed.wait(&mut dirty_pages);
        }
    }

    fn spawn_threads(&self) {
        let num_threads = self.thread_pool.current_num_threads();
        for _ in 0..num_threads {
            let inner_clone = Arc::clone(&self.inner);
            self.thread_pool.spawn(move || inner_clone.sync_thread());
        }
    }

    fn stop_threads(&self) {
        // Set the quit flag and then wake up all threads
        self.inner.quit.store(true, Ordering::Relaxed);
        self.inner.new_dirty_page.notify_all();

        // Wait for all threads to quit
        loop {
            let mut dirty_pages = self.inner.dirty_pages.lock();
            if self.inner.active_threads.load(Ordering::Relaxed) == 0 {
                break;
            }
            self.inner.new_dirty_page.notify_all();
            self.inner.dirty_pages_consumed.wait(&mut dirty_pages);
        }
    }
}

impl PageSyncerInner {
    fn sync_thread(&self) {
        self.active_threads.fetch_add(1, Ordering::Relaxed);

        loop {
            let range = {
                let mut dirty_pages = self.dirty_pages.lock();
                if dirty_pages.is_empty() {
                    // Let `sync()` know that `dirty_pages` is empty
                    self.dirty_pages_consumed.notify_all();
                    if self.quit.load(Ordering::Relaxed) {
                        // `dirty_pages` is empty, and we've been asked by `stop_threads()` to quit
                        break;
                    }
                    // Wait for `dirty_pages` to be populated
                    self.new_dirty_page.wait(&mut dirty_pages);
                }
                // Get a chunk of dirty pages, and drop the lock (this is done implicitly as we
                // exit the scope)
                self.pop_dirty_pages(&mut dirty_pages)
            };
            if let Some((start, count)) = range {
                self.sync_range(start, count);
            }
        }

        // Decrement the thread count and send an extra notification so that `stop_threads()` can
        // verify if `active_threads` has reached 0.
        //
        // In order to successfully synchronize with `stop_threads()`, we must hold a lock to
        // `dirty_pages`, otherwise the risk is that the threads can quit after the
        // `stop_threads()` has checked the thread count, but before it starts waiting, causing
        // `stop_threads()` to be stuck forever.
        let dirty_pages = self.dirty_pages.lock();
        self.active_threads.fetch_sub(1, Ordering::Relaxed);
        self.dirty_pages_consumed.notify_all();
        drop(dirty_pages);
    }

    /// Pops a contiguous chunk of pages from the `dirty_pages` set.
    ///
    /// The returned value (if any) is a pair `(start, count)`, where `start` is the first page to
    /// be synced, and `count` is the number of pages (including `start`) to sync after the first
    /// page.
    #[must_use]
    fn pop_dirty_pages(
        &self,
        dirty_pages: &mut MutexGuard<'_, BTreeSet<PageId>>,
    ) -> Option<(PageId, usize)> {
        let start = dirty_pages.pop_first()?;
        let mut end = start;
        while end.as_u32() - start.as_u32() < MAX_PAGE_COUNT {
            if let Some(next_page_id) = dirty_pages.first() {
                if next_page_id.as_u32() == end.as_u32() + 1 {
                    end = *next_page_id;
                    dirty_pages.pop_first();
                    continue;
                }
            }
            break;
        }

        let count = end.as_usize() - start.as_usize() + 1;
        Some((start, count))
    }

    /// Calls `msync()` on a range of pages.
    fn sync_range(&self, start: PageId, count: usize) {
        let byte_start = start.as_offset();
        let byte_len = count * Page::SIZE;
        if cfg!(not(miri)) {
            if let Err(err) = self.mmap.flush_range(byte_start, byte_len) {
                let byte_end = byte_start.saturating_add(byte_len);
                // TODO: use `log::error!` instead
                eprintln!("failed to sync pages to secondary storage (range: 0x{byte_start:x}..0x{byte_end:x}): {err}");
            }
        }
    }
}

impl Drop for PageSyncer {
    fn drop(&mut self) {
        self.stop_threads();
        self.sync();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::page_id;
    use memmap2::MmapOptions;

    #[must_use]
    fn new_mmap() -> MmapRaw {
        MmapOptions::new()
            .len(10 * Page::SIZE)
            .map_anon()
            .expect("failed to create memory map")
            .into()
    }

    #[test]
    fn drop_stops_all_threads() {
        let num_threads = 16;
        let syncer = PageSyncer::new(new_mmap(), NonZero::new(num_threads).unwrap())
            .expect("syncer creation failed");

        // Obtain a weak reference to the inner struct. This struct is used by all background
        // threads, which hold a strong reference to it, so if this weak reference becomes invalid
        // later on it means that all threads have correctly stopped.
        let inner = Arc::downgrade(&syncer.inner);

        assert_eq!(inner.strong_count(), num_threads + 1);

        drop(syncer);

        assert_eq!(inner.strong_count(), 0);
    }

    #[test]
    fn pop_dirty_pages_returns_contiguous_ranges() {
        let num_threads = 16;
        let syncer = PageSyncer::new(new_mmap(), NonZero::new(num_threads).unwrap())
            .expect("syncer creation failed");
        syncer.stop_threads();

        syncer.mark_dirty(page_id!(1));
        syncer.mark_dirty(page_id!(3));
        syncer.mark_dirty(page_id!(5));
        syncer.mark_dirty(page_id!(7));
        syncer.mark_dirty(page_id!(9));

        syncer.mark_dirty(page_id!(4));
        syncer.mark_dirty(page_id!(8));
        syncer.mark_dirty(page_id!(10));

        let mut dirty_pages = syncer.inner.dirty_pages.lock();

        assert_eq!(syncer.inner.pop_dirty_pages(&mut dirty_pages), Some((page_id!(1), 1)));
        assert_eq!(syncer.inner.pop_dirty_pages(&mut dirty_pages), Some((page_id!(3), 3)));
        assert_eq!(syncer.inner.pop_dirty_pages(&mut dirty_pages), Some((page_id!(7), 4)));
        assert_eq!(syncer.inner.pop_dirty_pages(&mut dirty_pages), None);
    }
}
