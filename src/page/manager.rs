pub(super) mod mmap;
pub(super) mod options;

/// Type alias for page ids.
/// Currently we use 4 bytes for page ids, which implies a maximum of 16TB of data.
pub type PageId = u32;

/// Represents various errors that might arise from page operations.
#[derive(Debug)]
pub enum PageError {
    PageNotFound(PageId),
    OutOfBounds(PageId),
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
