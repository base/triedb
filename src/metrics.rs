use metrics::{Counter, Histogram};
use metrics_derive::Metrics;
use std::cell::Cell;

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

#[derive(Default, Clone, Debug)]
pub(crate) struct TransactionMetrics {
    pages_read: Cell<u32>,
    pages_allocated: Cell<u32>,
    pages_reallocated: Cell<u32>,
    pages_split: Cell<u32>,
    cache_storage_read_hit: Cell<u32>,
    cache_storage_read_miss: Cell<u32>,
}

impl TransactionMetrics {
    pub(crate) fn inc_pages_read(&self) {
        self.pages_read.set(self.pages_read.get() + 1);
    }

    pub(crate) fn inc_pages_split(&self) {
        self.pages_split.set(self.pages_split.get() + 1);
    }

    pub(crate) fn inc_pages_allocated(&self) {
        self.pages_allocated.set(self.pages_allocated.get() + 1);
    }

    pub(crate) fn inc_pages_reallocated(&self) {
        self.pages_reallocated.set(self.pages_reallocated.get() + 1);
    }

    /// Increment the cache storage read hit
    pub(crate) fn inc_cache_storage_read_hit(&self) {
        self.cache_storage_read_hit.set(self.cache_storage_read_hit.get() + 1);
    }

    /// Increment the cache storage read miss
    pub(crate) fn inc_cache_storage_read_miss(&self) {
        self.cache_storage_read_miss.set(self.cache_storage_read_miss.get() + 1);
    }

    pub(crate) fn take_pages_read(&self) -> u32 {
        self.pages_read.take()
    }

    pub(crate) fn take_pages_split(&self) -> u32 {
        self.pages_split.take()
    }

    pub(crate) fn take_pages_allocated(&self) -> u32 {
        self.pages_allocated.take()
    }

    pub(crate) fn take_pages_reallocated(&self) -> u32 {
        self.pages_reallocated.take()
    }

    /// Take the cache storage read hit and miss
    pub(crate) fn take_cache_storage_read(&self) -> (u32, u32) {
        (self.cache_storage_read_hit.take(), self.cache_storage_read_miss.take())
    }

    #[cfg(test)]
    pub(crate) fn get_pages_read(&self) -> u32 {
        self.pages_read.get()
    }

    #[cfg(test)]
    pub(crate) fn get_pages_split(&self) -> u32 {
        self.pages_split.get()
    }

    #[cfg(test)]
    pub(crate) fn get_pages_allocated(&self) -> u32 {
        self.pages_allocated.get()
    }

    #[cfg(test)]
    pub(crate) fn get_pages_reallocated(&self) -> u32 {
        self.pages_reallocated.get()
    }

    #[cfg(test)]
    pub(crate) fn get_cache_storage_read(&self) -> (u32, u32) {
        (self.cache_storage_read_hit.get(), self.cache_storage_read_miss.get())
    }
}
