use crate::page::PageId;
use std::{io, sync::Arc};

pub(super) mod mmap;
pub(super) mod options;

impl From<io::Error> for PageError {
    fn from(error: io::Error) -> Self {
        Self::IO(error.into())
    }
}

/// Represents various errors that might arise from page operations.
#[derive(Clone, Debug)]
pub enum PageError {
    PageNotFound(PageId),
    PageLimitReached,
    InvalidRootPage(PageId),
    InvalidCellPointer,
    NoFreeCells,
    PageIsFull,
    PageSplitLimitReached,
    IO(Arc<io::Error>),
    InvalidValue,
    InvalidPageContents(PageId),
    // TODO: add more errors here for other cases.
}
