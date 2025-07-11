use crate::metrics::DatabaseMetrics;
use log::{Level, LevelFilter, Log, Metadata, Record};
use std::io::Write;

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
        }
    }
}

/// A configurable logger.
#[derive(Debug)]
pub struct Logger;

impl Log for Logger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= Level::Info
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            println!("[{}] {} - {}", record.level(), record.target(), record.args());
        }
    }

    fn flush(&self) {
        std::io::stdout().flush().unwrap();
    }
}