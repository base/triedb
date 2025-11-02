use std::fmt;

use dashmap::DashMap;
use evict::{EvictResult, EvictionPolicy, LruReplacer};
use fxhash::FxBuildHasher;
use parking_lot::Mutex;

use crate::page::{
    manager::buffer_pool::{FrameId, FxMap},
    PageId,
};

// TODO: Temporarily use LruReplacer as the eviction policy, replace with a better eviction policy
pub(crate) struct CacheEvict {
    lru_replacer: LruReplacer<PageId>,
    read_frames: Mutex<Vec<PageId>>,
    pub(crate) update_frames: FxMap<PageId, FrameId>,
    pub(crate) new_frames: Mutex<Vec<(FrameId, PageId)>>,
}

impl fmt::Debug for CacheEvict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CacheEvict")
    }
}

impl CacheEvict {
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            lru_replacer: LruReplacer::new(capacity),
            read_frames: Mutex::new(Vec::with_capacity(capacity)),
            update_frames: DashMap::with_capacity_and_hasher(capacity, FxBuildHasher::default()),
            new_frames: Mutex::new(Vec::with_capacity(capacity)),
        }
    }

    pub(crate) fn evict(&self) -> Option<PageId> {
        self.lru_replacer.evict()
    }

    pub(crate) fn touch(&self, page_id: PageId) -> EvictResult<(), PageId> {
        self.lru_replacer.touch(page_id)
    }

    pub(crate) fn pin_read(&self, page_id: PageId) -> EvictResult<(), PageId> {
        self.read_frames.lock().push(page_id);
        self.lru_replacer.pin(page_id)
    }

    pub(crate) fn pin_write_update_page(
        &self,
        frame_id: FrameId,
        page_id: PageId,
    ) -> EvictResult<(), PageId> {
        if let Some((_, first_page_id)) = self.new_frames.lock().first() {
            if page_id.as_u32() < first_page_id.as_u32() {
                self.update_frames.insert(page_id, frame_id);
            }
        } else {
            self.update_frames.insert(page_id, frame_id);
        }

        self.lru_replacer.pin(page_id)
    }

    pub(crate) fn pin_write_new_page(
        &self,
        frame_id: FrameId,
        page_id: PageId,
    ) -> EvictResult<(), PageId> {
        let mut new_frames = self.new_frames.lock();
        if let Some((_, last_page_id)) = new_frames.last() {
            debug_assert!(
                last_page_id.as_u32() + 1 == page_id,
                "page_id: {:?}, last_page_id: {:?}",
                page_id,
                last_page_id
            );
        }
        new_frames.push((frame_id, page_id));

        self.lru_replacer.pin(page_id)
    }

    pub(crate) fn unpin(&self, page_id: PageId) -> EvictResult<(), PageId> {
        self.lru_replacer.unpin(page_id)
    }
}
