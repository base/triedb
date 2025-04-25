use crate::page::PageId;

pub(super) mod mmap;
pub(super) mod options;

/// Represents various errors that might arise from page operations.
#[derive(Debug)]
pub enum PageError {
    PageNotFound(PageId),
    PageLimitReached,
    InvalidRootPage(PageId),
    InvalidCellPointer,
    NoFreeCells,
    PageIsFull,
    PageSplitLimitReached,
    IO(std::io::Error),
    InvalidValue,
    InvalidPageContents(PageId),
    // TODO: add more errors here for other cases.
}
