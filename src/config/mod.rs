use log::LevelFilter;
use crate::context::B512Map;
use crate::page::PageId;
use crate::snapshot::SnapshotId;

pub mod metrics;
pub mod logger;
pub mod cache;

pub use metrics::MetricsCollector;
pub use cache::CacheManager;

/// Config lets you control certain aspects like cache parameters, log level, metrics 
/// collection, and concurrency. It is passed in during opening of the database.
#[derive(Debug, Clone)]
pub struct Config {
    /// The maximum size of the LRU cache for per-transaction mapping.
    pub max_lru_size: usize,
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
    pub fn with_max_lru_size(mut self, max_lru_size: usize) -> Self {
        self.max_lru_size = max_lru_size;
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
            max_lru_size: 1024, // TODO: not sure what the default should be
            // There is always at most 1 writer.
            max_concurrent_transactions: usize::MAX,
            // Currently, we expose at most 1 writer at a given time.
            max_writers: 1,
            log_level: LevelFilter::Info,
            metrics_collector: MetricsCollector::default(),
            cache_manager: CacheManager::default(),
        }
    }
}
