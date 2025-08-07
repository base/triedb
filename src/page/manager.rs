use crate::page::PageId;
use rayon::ThreadPoolBuildError;

pub(super) mod mmap;
pub(super) mod options;
pub(super) mod syncer;

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
    ThreadPoolError(ThreadPoolBuildError),
    InvalidValue,
    InvalidPageContents(PageId),
    // TODO: add more errors here for other cases.
}
