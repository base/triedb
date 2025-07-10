use crate::metrics::DatabaseMetrics;
use std::time::Duration;

/// Config lets you control certain aspects like caching, logging, metrics, and concurrency.
#[derive(Debug, Clone)]
pub struct Config {
    pub log_level: LogLevel,
    pub caching: CachingConfig,
    pub metrics: DatabaseMetrics,
    pub concurrency: ConcurrencyConfig,
}

#[derive(Debug, Clone)]
pub enum LogLevel {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}

#[derive(Debug, Clone)]
pub struct CachingConfig {
    pub page_cache_size: usize,
    pub node_cache_size: usize,
    pub storage_cache_size: usize,
}

#[derive(Debug, Clone)]
pub struct ConcurrencyConfig {
    pub max_concurrent_transactions: usize,
    pub background_threads: usize,
    pub lock_timeout: Duration,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            caching: CachingConfig::default(),
            log_level: LogLevel::Info,
            metrics: DatabaseMetrics::default(),
            concurrency: ConcurrencyConfig::default(),
        }
    }
}

impl Default for CachingConfig {
    fn default() -> Self {
        Self {
            page_cache_size: 1024 * 1024, // 1MB
            node_cache_size: 512 * 1024,  // 512KB
            storage_cache_size: 2 * 1024 * 1024, // 2MB
        }
    }
}

impl Default for ConcurrencyConfig {
    fn default() -> Self {
        Self {
            max_concurrent_transactions: 100,
            background_threads: 4,
            lock_timeout: Duration::from_secs(30),
        }
    }
}

impl Config {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_caching(mut self, caching: CachingConfig) -> Self {
        self.caching = caching;
        self
    }

    pub fn with_log_level(mut self, log_level: LogLevel) -> Self {
        self.log_level = log_level;
        self
    }

    pub fn with_concurrency(mut self, concurrency: ConcurrencyConfig) -> Self {
        self.concurrency = concurrency;
        self
    }
}