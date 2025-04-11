use std::mem;

use metrics::{Counter, Histogram};
use metrics_derive::Metrics;

use parking_lot::RwLock;

#[derive(Metrics, Clone)]
#[metrics(scope = "triedb")]
pub(crate) struct DatabaseMetrics {
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

// Compile-time assertion to ensure that `TransactionMetricsInner` is `Sync`
const _: fn() = || {
    fn consumer<T: Sync + Send>() {}
    consumer::<TransactionMetricsInner>();
    consumer::<TransactionMetricsInner>();
};

#[derive(Debug, Default)]
pub(crate) struct TransactionMetrics {
    inner: RwLock<TransactionMetricsInner>,
}

impl TransactionMetrics {
    pub(crate) fn inc_pages_read(&self) {
        self.inner.write().pages_read += 1;
    }

    pub(crate) fn inc_pages_split(&self) {
        self.inner.write().pages_split += 1;
    }

    pub(crate) fn inc_pages_allocated(&self) {
        self.inner.write().pages_allocated += 1;
    }

    pub(crate) fn inc_pages_reallocated(&self) {
        self.inner.write().pages_reallocated += 1;
    }

    /// Increment the cache storage read hit
    pub(crate) fn inc_cache_storage_read_hit(&self) {
        self.inner.write().cache_storage_read_hit += 1;
    }

    /// Increment the cache storage read miss
    pub(crate) fn inc_cache_storage_read_miss(&self) {
        self.inner.write().cache_storage_read_miss += 1;
    }

    pub(crate) fn take_pages_read(&self) -> u32 {
        let mut inner = self.inner.write();
        mem::take(&mut inner.pages_read)
    }

    pub(crate) fn take_pages_split(&self) -> u32 {
        let mut inner = self.inner.write();
        mem::take(&mut inner.pages_split)
    }

    pub(crate) fn take_pages_allocated(&self) -> u32 {
        let mut inner = self.inner.write();
        mem::take(&mut inner.pages_allocated)
    }

    pub(crate) fn take_pages_reallocated(&self) -> u32 {
        let mut inner = self.inner.write();
        mem::take(&mut inner.pages_reallocated)
    }

    /// Take the cache storage read hit and miss
    pub(crate) fn take_cache_storage_read(&self) -> (u32, u32) {
        let mut inner = self.inner.write();
        let cache_storage_read_hit = mem::take(&mut inner.cache_storage_read_hit);
        let cache_storage_read_miss = mem::take(&mut inner.cache_storage_read_miss);
        (cache_storage_read_hit, cache_storage_read_miss)
    }

    #[cfg(test)]
    pub(crate) fn get_pages_read(&self) -> u32 {
        self.inner.read().pages_read
    }

    #[cfg(test)]
    pub(crate) fn get_pages_split(&self) -> u32 {
        self.inner.read().pages_split
    }

    #[cfg(test)]
    pub(crate) fn get_pages_allocated(&self) -> u32 {
        self.inner.read().pages_allocated
    }

    #[cfg(test)]
    pub(crate) fn get_pages_reallocated(&self) -> u32 {
        self.inner.read().pages_reallocated
    }

    #[cfg(test)]
    pub(crate) fn get_cache_storage_read(&self) -> (u32, u32) {
        let metrics = self.inner.read();
        (metrics.cache_storage_read_hit, metrics.cache_storage_read_miss)
    }
}
