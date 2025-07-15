use std::os::unix::net::SocketAddr;

use crate::page::Page;
use log::LevelFilter;

/// Config lets you control certain aspects like log level, metrics
/// address, and concurrency. It is passed in during opening of the database.
#[derive(Debug, Clone)]
pub struct Config {
    /// The maximum number of pages that can be allocated.
    max_pages: u32,
    /// The maximum number of entries for a single snapshot cache.
    max_cache_size: usize,
    /// The limit on total number of concurrent transactions.
    max_concurrent_transactions: usize,
    /// The limit on number of threads in the writer's internal thread pool.
    max_writers: usize,
    /// The log level for the database.
    log_level: LevelFilter,
    /// The metrics address to export to.
    metrics_address: Option<SocketAddr>,
}

impl Config {
    // Setters
    pub fn with_max_pages(mut self, max_pages: u32) -> Self {
        self.max_pages = max_pages;
        self
    }

    pub fn with_max_cache_size(mut self, max_cache_size: usize) -> Self {
        self.max_cache_size = max_cache_size;
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

    pub fn with_metrics_address(mut self, metrics_address: SocketAddr) -> Self {
        self.metrics_address = Some(metrics_address);
        self
    }

    // Getters
    pub const fn max_pages(&self) -> u32 {
        self.max_pages
    }

    pub const fn max_concurrent_transactions(&self) -> usize {
        self.max_concurrent_transactions
    }

    pub const fn max_writers(&self) -> usize {
        self.max_writers
    }

    pub const fn log_level(&self) -> LevelFilter {
        self.log_level
    }

    pub fn metrics_address(&self) -> Option<SocketAddr> {
        self.metrics_address.clone()
    }
}

impl Default for Config {
    fn default() -> Self {
        Self {
            // Let user outside of database to set this
            max_pages: Page::MAX_COUNT,
            max_cache_size: 10,
            // This would default to an unlimited number (always at most 1 writer)
            max_concurrent_transactions: usize::MAX,
            // Currently, we expose at most 1 writer at a given time.
            max_writers: 1,
            log_level: LevelFilter::Info,
            metrics_address: None,
        }
    }
}
