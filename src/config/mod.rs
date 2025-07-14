use crate::{
    context::B512Map,
    page::{Page, PageId},
    snapshot::SnapshotId,
};
use log::LevelFilter;

pub mod cache;
pub mod logger;
pub mod metrics;

pub use cache::CacheManager;
pub use metrics::MetricsCollector;

/// Config lets you control certain aspects like cache parameters, log level, metrics
/// collection, and concurrency. It is passed in during opening of the database.
#[derive(Debug, Clone)]
pub struct Config {
    /// The maximum number of pages that can be allocated.
    pub max_pages: u32,
    /// The limit on total number of concurrent transactions.
    pub max_concurrent_transactions: usize,
    /// The limit on number of threads in the writer's internal thread pool.
    pub max_writers: usize,
    /// The log level for the database.
    pub log_level: LevelFilter,
    /// The configuration options for metrics collection.
    pub metrics_collector: MetricsCollector,
    /// The central cache manager for account-location mapping organized by snapshot ID.
    cache_manager: CacheManager,
}

impl Config {
    pub fn new() -> Self {
        Self::default()
    }

    // Setters
    /// Sets the maximum number of pages that can be allocated to this file.
    ///
    /// The default is [`PageId::MAX`].
    pub fn with_max_pages(mut self, max_pages: u32) -> Self {
        self.max_pages = max_pages;
        self
    }

    pub fn with_max_concurrent_transactions(mut self, max_concurrent_transactions: usize) -> Self {
        self.max_concurrent_transactions = max_concurrent_transactions;
        self
    }

    pub fn with_max_writers(mut self, max_writers: usize) -> Self {
        self.max_writers = max_writers;
        self
    }

    pub fn with_log_level(mut self, log_level: LevelFilter) -> Self {
        self.log_level = log_level;
        self
    }

    pub fn with_metrics_collector(mut self, metrics_collector: MetricsCollector) -> Self {
        self.metrics_collector = metrics_collector;
        self
    }

    pub fn with_cache_manager(mut self, cache_manager: CacheManager) -> Self {
        self.cache_manager = cache_manager;
        self
    }

    /// Commit a writer transaction's cache as the new baseline
    pub fn save_cache(&mut self, snapshot_id: SnapshotId) {
        self.cache_manager.save_cache(snapshot_id);
    }

    /// Clear a specific snapshot's cache
    pub fn clear_cache(&mut self, snapshot_id: SnapshotId) {
        self.cache_manager.clear_cache(snapshot_id);
    }

    // Getters
    /// Get a cache for the given snapshot ID
    pub fn get_cache(&mut self, snapshot_id: SnapshotId) -> &mut B512Map<(PageId, u8)> {
        self.cache_manager.get_cache(snapshot_id)
    }
}

impl Default for Config {
    fn default() -> Self {
        Self {
            max_pages: if cfg!(not(test)) {
                Page::MAX_COUNT
            } else {
                // Because tests run in parallel, it's easy to exhaust the address space, so use a
                // more conservative limit
                Page::MAX_COUNT / 1024
            },
            // This would default to an unlimited number (always at most 1 writer)
            max_concurrent_transactions: usize::MAX,
            // Currently, we expose at most 1 writer at a given time.
            max_writers: 1,
            log_level: LevelFilter::Info,
            metrics_collector: MetricsCollector::default(),
            cache_manager: CacheManager::default(),
        }
    }
}
