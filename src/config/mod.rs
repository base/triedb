use crate::metrics::DatabaseMetrics;
use log::LevelFilter;

pub mod metrics;
pub mod logger;

pub use metrics::MetricsCollector;

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
    /// The metrics configuration.
    pub metrics: DatabaseMetrics,
    /// The configurable metrics collector configuration.
    pub metrics_collector: MetricsCollector,
}

impl Config {
    pub fn new() -> Self {
        Self::default()
    }

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

    pub fn with_metrics(mut self, metrics: DatabaseMetrics) -> Self {
        self.metrics = metrics;
        self
    }

    pub fn with_metrics_collector(mut self, metrics_collector: MetricsCollector) -> Self {
        self.metrics_collector = metrics_collector;
        self
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
            metrics: DatabaseMetrics::default(),
            metrics_collector: MetricsCollector::default(),
        }
    }
}
