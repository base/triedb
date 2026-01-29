use crate::page::PageId;
use thiserror::Error;

mod dirty;
pub(super) mod mmap;
pub(super) mod options;

/// Represents various errors that might arise from page operations.
#[derive(Debug, Error)]
pub enum PageError {
    #[error("page not found: {0}")]
    PageNotFound(PageId),
    #[error("page occupied: {0}")]
    PageOccupied(PageId),
    #[error("page dirty: {0}")]
    PageDirty(PageId),
    #[error("page limit reached")]
    PageLimitReached,
    #[error("invalid root page: {0}")]
    InvalidRootPage(PageId),
    #[error("invalid cell pointer")]
    InvalidCellPointer,
    #[error("no free cells")]
    NoFreeCells,
    #[error("page is full")]
    PageIsFull,
    #[error("page split limit reached")]
    PageSplitLimitReached,
    #[error("I/O error: {0}")]
    IO(#[from] std::io::Error),
    #[error("invalid value")]
    InvalidValue,
    #[error("invalid page contents: {0}")]
    InvalidPageContents(PageId),
    // TODO: add more errors here for other cases.
}
