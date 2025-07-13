use crate::{config::Config, page::{PageError, PageManager}};
use std::{
    fs::{File, OpenOptions},
    path::Path,
};

#[derive(Clone, Debug)]
pub struct PageManagerOptions {
    pub(super) open_options: OpenOptions,
    pub(super) page_count: u32,
}

impl PageManagerOptions {
    pub fn new() -> Self {
        let mut open_options = File::options();
        open_options.read(true).write(true).create(true).truncate(false);

        Self { open_options, page_count: 0 }
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

    /// Causes the file length to be set to 0 after opening it.
    ///
    /// Note that if `wipe(true)` is set, then setting [`page_count()`](Self::page_count) with any
    /// number greater than `0` will cause the open to fail.
    pub fn wipe(&mut self, wipe: bool) -> &mut Self {
        self.open_options.truncate(wipe);
        self
    }

    /// Opens the file at `path` with the options specified by `self`.
    pub fn open(&self, cfg: &Config, path: impl AsRef<Path>) -> Result<PageManager, PageError> {
        PageManager::open_with_options(self, cfg, path)
    }

    /// Wraps the given `file` with the options specified by `self`.
    ///
    /// If `.wrap()` is called, `.create()` and `.create_new()` are ignored.
    pub fn wrap(&self, cfg: &Config, file: File) -> Result<PageManager, PageError> {
        PageManager::from_file_with_options(self, cfg, file)
    }

    /// Opens a temporary file with the options specified by `self`.
    #[cfg(test)]
    pub fn open_temp_file(&self, cfg: &Config) -> Result<PageManager, PageError> {
        let file = tempfile::tempfile().map_err(PageError::IO)?;
        self.wrap(cfg, file)
    }
}

impl Default for PageManagerOptions {
    fn default() -> Self {
        Self::new()
    }
}
