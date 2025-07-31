use std::io;

use crate::{
    page::{Page, PageId, PageMut},
    snapshot::SnapshotId,
};

pub(super) mod buffer_pool;
pub(super) mod mmap;
pub(super) mod options;

/// Represents various errors that might arise from page operations.
#[derive(Debug)]
pub enum PageError {
    PageNotFound(PageId),
    PageOccupied(PageId),
    PageDirty(PageId),
    PageLimitReached,
    InvalidRootPage(PageId),
    InvalidCellPointer,
    NoFreeCells,
    PageIsFull,
    PageSplitLimitReached,
    IO(std::io::Error),
    InvalidValue,
    InvalidPageContents(PageId),
    OutOfMemory,
    EvictionPolicy,
    // TODO: add more errors here for other cases.
}

pub trait PageManagerTrait: Send + Sync + std::fmt::Debug + 'static {
    /// Retrieves a read-only page from the page manager
    fn get(&self, snapshot_id: SnapshotId, page_id: PageId) -> Result<Page<'_>, PageError>;

    /// Retrieves a mutable page from the page manager
    fn get_mut(&self, snapshot_id: SnapshotId, page_id: PageId) -> Result<PageMut<'_>, PageError>;

    /// Allocates a new page
    fn allocate(&self, snapshot_id: SnapshotId) -> Result<PageMut<'_>, PageError>;

    /// Returns the number of pages currently stored
    fn size(&self) -> u32;

    /// Returns the maximum number of pages that can be allocated
    fn capacity(&self) -> u32;

    /// Syncs pages to the backing store
    fn sync(&self) -> io::Result<()>;

    /// Syncs and closes the page manager
    fn close(self: Box<Self>) -> io::Result<()>;
}
