use std::fmt;

use evict::{EvictResult, EvictionPolicy, LruReplacer};

use crate::page::PageId;

pub(crate) struct CacheEvict(LruReplacer<PageId>);

impl fmt::Debug for CacheEvict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CacheEvict")
    }
}

impl CacheEvict {
    pub(crate) fn new(capacity: usize) -> Self {
        Self(LruReplacer::new(capacity))
    }

    pub(crate) fn evict(&self) -> Option<PageId> {
        self.0.evict()
    }

    pub(crate) fn touch(&self, page_id: PageId) -> EvictResult<(), PageId> {
        self.0.touch(page_id)
    }

    pub(crate) fn pin(&self, page_id: PageId) -> EvictResult<(), PageId> {
        self.0.pin(page_id)
    }

    pub(crate) fn unpin(&self, page_id: PageId) -> EvictResult<(), PageId> {
        self.0.unpin(page_id)
    }
}
