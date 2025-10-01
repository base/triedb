use std::{fmt, ptr::NonNull};

use dashmap::DashMap;
use evict::{EvictResult, EvictionPolicy, LruReplacer};
use parking_lot::Mutex;

use crate::page::{manager::buffer_pool::FrameId, PageId};

// TODO: Temporarily use LruReplacer as the eviction policy, replace with a better eviction policy
pub(crate) struct CacheEvict {
    lru_replacer: LruReplacer<PageId>,
    read_frames: Mutex<Vec<PageId>>,
    pub(crate) write_frames: Mutex<Vec<(FrameId, PageId)>>,
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
            write_frames: Mutex::new(Vec::with_capacity(capacity)),
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

    pub(crate) fn pin_write(&self, frame_id: FrameId, page_id: PageId) -> EvictResult<(), PageId> {
        self.write_frames.lock().push((frame_id, page_id));
        self.lru_replacer.pin(page_id)
    }

    pub(crate) fn unpin(&self, page_id: PageId) -> EvictResult<(), PageId> {
        self.lru_replacer.unpin(page_id)
    }
}

pub type DefaultHasher = std::collections::hash_map::RandomState;

struct KeyRef<K> {
    k: *const K,
}

pub struct LruEntry<K> {
    key: me,
}

pub struct LruCache<K, S = DefaultHasher> {
    map: DashMap<KeyRef<K>, NonNull<LruEntry<K>>, S>,
    cap: NonZeroUsize,
    head: *mut LruEntry<K>,
    tail: *mut LruEntry<K>,
}
