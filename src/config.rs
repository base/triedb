use crate::page::Page;
use log::LevelFilter;

/// Config lets you control certain aspects like log level, metrics
/// address, and concurrency. It is passed in during opening of the database.
#[derive(Debug, Clone)]
pub struct Config {
    /// The maximum number of pages that can be allocated.
    max_pages: u32,
    /// The log level for the database.
    log_level: LevelFilter,
}

impl Config {
    // Setters
    pub fn with_max_pages(mut self, max_pages: u32) -> Self {
        self.max_pages = max_pages;
        self
    }

    pub fn with_log_level(mut self, log_level: LevelFilter) -> Self {
        self.log_level = log_level;
        self
    }

    // Getters
    pub const fn max_pages(&self) -> u32 {
        self.max_pages
    }

    pub const fn log_level(&self) -> LevelFilter {
        self.log_level
    }
}

impl Default for Config {
    fn default() -> Self {
        Self { max_pages: Page::MAX_COUNT, log_level: LevelFilter::Info }
    }
}
