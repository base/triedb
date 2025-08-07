use crate::page::{Page, PageError, PageManager};
use std::{
    fs::{File, OpenOptions},
    num::NonZero,
    path::Path,
};

#[derive(Clone, Debug)]
pub struct PageManagerOptions {
    pub(super) open_options: OpenOptions,
    pub(super) page_count: u32,
    pub(super) max_pages: u32,
    pub(super) io_parallelism: NonZero<usize>,
}

impl PageManagerOptions {
    pub fn new() -> Self {
        let mut open_options = File::options();
        open_options.read(true).write(true).create(true).truncate(false);

        let max_pages = if cfg!(not(test)) {
            Page::MAX_COUNT
        } else {
            // Because tests run in parallel, it's easy to exhaust the address space, so use a more
            // conservative limit
            Page::MAX_COUNT / 1024
        };

        Self { open_options, page_count: 0, max_pages, io_parallelism: NonZero::new(128).unwrap() }
    }

    /// Sets the option to create a new file, or open it if it already exists.
    ///
    /// The default is `true`.
    pub fn create(&mut self, create: bool) -> &mut Self {
        self.open_options.create(create);
        self
    }

    /// Sets the option to create a new file, failing if it already exists.
    ///
    /// The default is `false`.
    ///
    /// If `.create_new(true)` is set, then `.create()` is ignored.
    pub fn create_new(&mut self, create_new: bool) -> &mut Self {
        self.open_options.create_new(create_new);
        self
    }

    /// Sets the number of pages already written to the file.
    ///
    /// The default is `0`.
    pub fn page_count(&mut self, page_count: u32) -> &mut Self {
        self.page_count = page_count;
        self
    }

    /// Sets the maximum number of pages that can be allocated to this file.
    ///
    /// The default is [`PageId::MAX`].
    pub fn max_pages(&mut self, max_pages: u32) -> &mut Self {
        self.max_pages = max_pages;
        self
    }

    /// Causes the file length to be set to 0 after opening it.
    ///
    /// Note that if `wipe(true)` is set, then setting [`page_count()`](Self::page_count) with any
    /// number greater than `0` will cause the open to fail.
    pub fn wipe(&mut self, wipe: bool) -> &mut Self {
        self.open_options.truncate(wipe);
        self
    }

    /// Sets the maximum amount I/O parallelism that can be used during writes.
    ///
    /// This specifies the maximum number of *pages* that can be written in parallel at any given
    /// time.
    ///
    /// By default, `io_parallelism` is set to 128, although this default may change in the future.
    pub fn io_parallelism(&mut self, io_parallelism: NonZero<usize>) -> &mut Self {
        self.io_parallelism = io_parallelism;
        self
    }

    /// Opens the file at `path` with the options specified by `self`.
    pub fn open(&self, path: impl AsRef<Path>) -> Result<PageManager, PageError> {
        PageManager::open_with_options(self, path)
    }

    /// Wraps the given `file` with the options specified by `self`.
    ///
    /// If `.wrap()` is called, `.create()` and `.create_new()` are ignored.
    pub fn wrap(&self, file: File) -> Result<PageManager, PageError> {
        PageManager::from_file_with_options(self, file)
    }

    /// Opens a temporary file with the options specified by `self`.
    #[cfg(test)]
    pub fn open_temp_file(&self) -> Result<PageManager, PageError> {
        let file = tempfile::tempfile().map_err(PageError::IO)?;
        self.wrap(file)
    }
}

impl Default for PageManagerOptions {
    fn default() -> Self {
        Self::new()
    }
}
