use crate::page::PageId;

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
    // TODO: add more errors here for other cases.
}

impl Clone for PageError {
    fn clone(&self) -> Self {
        match self {
            Self::PageNotFound(id) => Self::PageNotFound(*id),
            Self::PageOccupied(id) => Self::PageOccupied(*id),
            Self::PageDirty(id) => Self::PageDirty(*id),
            Self::PageLimitReached => Self::PageLimitReached,
            Self::InvalidRootPage(id) => Self::InvalidRootPage(*id),
            Self::InvalidCellPointer => Self::InvalidCellPointer,
            Self::NoFreeCells => Self::NoFreeCells,
            Self::PageIsFull => Self::PageIsFull,
            Self::PageSplitLimitReached => Self::PageSplitLimitReached,
            Self::IO(e) => Self::IO(std::io::Error::new(e.kind(), e.to_string())),
            Self::InvalidValue => Self::InvalidValue,
            Self::InvalidPageContents(id) => Self::InvalidPageContents(*id),
        }
    }
}
