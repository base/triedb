use crate::page::PageId;

#[cfg(feature = "buffer_pool_backend")]
pub(super) mod buffer_pool;
#[cfg(feature = "buffer_pool_backend")]
pub(super) mod cache_evict;
// #[cfg(feature = "buffer_pool_backend")]
pub(super) mod clock_replacer;
#[cfg(feature = "mmap_backend")]
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
