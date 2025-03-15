use std::cell::RefCell;

use metrics::{Counter, Histogram};
use metrics_derive::Metrics;

#[derive(Metrics, Clone)]
#[metrics(scope = "triedb")]
pub struct DatabaseMetrics {
    /// The number of pages read by a read-only transaction
    #[metrics(describe = "The number of pages read by a read-only transaction")]
    pub(crate) ro_transaction_pages_read: Histogram,
    /// The number of pages read by a read-write transaction
    #[metrics(describe = "The number of pages read by a read-write transaction")]
    pub(crate) rw_transaction_pages_read: Histogram,
    /// The number of pages allocated by a read-write transaction
    #[metrics(describe = "The number of pages allocated by a read-write transaction")]
    pub(crate) rw_transaction_pages_allocated: Histogram,
    /// The number of pages reallocated by a read-write transaction
    #[metrics(describe = "The number of pages reallocated by a read-write transaction")]
    pub(crate) rw_transaction_pages_reallocated: Histogram,
    /// The number of pages split by a read-write transaction
    #[metrics(describe = "The number of pages split by a read-write transaction")]
    pub(crate) rw_transaction_pages_split: Histogram,
    /// The number of cache hits for storage read
    #[metrics(describe = "The number of cache hits for storage read")]
    pub(crate) cache_storage_read_hit: Counter,
    /// The number of cache misses for storage read
    #[metrics(describe = "The number of cache misses for storage read")]
    pub(crate) cache_storage_read_miss: Counter,
}

#[derive(Debug, Default, Clone)]
struct TransactionMetricsInner {
    pages_read: u32,
    pages_allocated: u32,
    pages_reallocated: u32,
    pages_split: u32,
    cache_storage_read_hit: u32,
    cache_storage_read_miss: u32,
}

#[derive(Debug, Default)]
pub(crate) struct TransactionMetrics {
    inner: RefCell<TransactionMetricsInner>,
}

impl TransactionMetrics {
    pub fn inc_pages_read(&self) {
        self.inner.borrow_mut().pages_read += 1;
    }

    pub fn inc_pages_split(&self) {
        self.inner.borrow_mut().pages_split += 1;
    }

    pub fn inc_pages_allocated(&self) {
        self.inner.borrow_mut().pages_allocated += 1;
    }

    pub fn inc_pages_reallocated(&self) {
        self.inner.borrow_mut().pages_reallocated += 1;
    }

    /// Increment the cache storage read hit
    pub fn inc_cache_storage_read_hit(&self) {
        self.inner.borrow_mut().cache_storage_read_hit += 1;
    }

    /// Increment the cache storage read miss
    pub fn inc_cache_storage_read_miss(&self) {
        self.inner.borrow_mut().cache_storage_read_miss += 1;
    }

    pub fn take_pages_read(&self) -> u32 {
        let mut metrics = self.inner.borrow_mut();
        let pages_read = metrics.pages_read;
        metrics.pages_read = 0;
        pages_read
    }

    pub fn take_pages_split(&self) -> u32 {
        let mut metrics = self.inner.borrow_mut();
        let pages_split = metrics.pages_split;
        metrics.pages_split = 0;
        pages_split
    }

    pub fn take_pages_allocated(&self) -> u32 {
        let mut metrics = self.inner.borrow_mut();
        let pages_allocated = metrics.pages_allocated;
        metrics.pages_allocated = 0;
        pages_allocated
    }

    pub fn take_pages_reallocated(&self) -> u32 {
        let mut metrics = self.inner.borrow_mut();
        let pages_reallocated = metrics.pages_reallocated;
        metrics.pages_reallocated = 0;
        pages_reallocated
    }

    /// Take the cache storage read hit and miss
    pub fn take_cache_storage_read(&self) -> (u32, u32) {
        let mut metrics = self.inner.borrow_mut();
        let cache_storage_read_hit = metrics.cache_storage_read_hit;
        let cache_storage_read_miss = metrics.cache_storage_read_miss;
        metrics.cache_storage_read_hit = 0;
        metrics.cache_storage_read_miss = 0;
        (cache_storage_read_hit, cache_storage_read_miss)
    }

    pub fn get_pages_read(&self) -> u32 {
        self.inner.borrow().pages_read
    }

    pub fn get_pages_split(&self) -> u32 {
        self.inner.borrow().pages_split
    }

    pub fn get_pages_allocated(&self) -> u32 {
        self.inner.borrow().pages_allocated
    }

    pub fn get_pages_reallocated(&self) -> u32 {
        self.inner.borrow().pages_reallocated
    }
}
