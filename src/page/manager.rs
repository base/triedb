use super::page::{Page, RO, RW};
use crate::snapshot::SnapshotId;
use std::fmt::Debug;
pub mod mmap;

/// currently we use 4 bytes for page ids, which implies a maximum of 16TB of data.
pub type PageId = u32;

/// Represents various errors that might arise from page operations.
#[derive(Debug)]
pub enum PageError {
    PageNotFound(PageId),
    OutOfBounds(PageId),
    InvalidRootPage(PageId),
    InvalidCellPointer,
    NoFreeCells,
    PageIsFull,
    IO(std::io::Error),
    InvalidValue,
    InvalidPageContents(PageId),
    // TODO: add more errors here for other cases.
}

/// Core trait that manages pages in trie db.
pub trait PageManager: Debug {
    /// Retrieves a page from the given snapshot.
    fn get<'p>(&self, snapshot_id: SnapshotId, page_id: PageId) -> Result<Page<'p, RO>, PageError>;

    /// Retrieves a mutable page from the given snapshot.
    fn get_mut<'p>(
        &mut self,
        snapshot_id: SnapshotId,
        page_id: PageId,
    ) -> Result<Page<'p, RW>, PageError>;

    /// Allocates a new page in the given snapshot.
    fn allocate<'p>(&mut self, snapshot_id: SnapshotId) -> Result<Page<'p, RW>, PageError>;

    /// Resizes the page manager to the given number of pages.
    fn resize(&mut self, new_page_count: PageId) -> Result<(), PageError>;

    /// Returns the total number of pages
    fn size(&self) -> u32;

    // /// Merges two pages into a new page.
    // fn merge(
    //     &mut self,
    //     snapshot_id: SnapshotId,
    //     page_a: PageId,
    //     page_b: PageId,
    //     page_out: PageId,
    // ) -> Result<(), PageError>;

    // /// Splits a page into two new pages.
    // fn split(
    //     &mut self,
    //     snapshot_id: SnapshotId,
    //     page_id: PageId,
    // ) -> Result<(PageId, PageId), PageError>;

    // /// Writes data to a page.
    // fn write(
    //     &mut self,
    //     snapshot_id: SnapshotId,
    //     page_id: PageId,
    //     data: &[u8],
    // ) -> Result<(), PageError>;

    /// Commits pages associated with a snapshot to durable storage.
    fn commit(&mut self, snapshot_id: SnapshotId) -> Result<(), PageError>;
}
