use std::fmt::Debug;
use crate::page::{Page, PageMut};
use crate::snapshot::SnapshotId;
mod mmap;
mod orphan_aware;

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
    // TODO: add more errors here for other cases.
}

/// Core trait that manages pages in trie db.
pub trait PageManager: Debug {
    /// Retrieves a page from the given snapshot.
    fn get(&self, snapshot_id: SnapshotId, page_id: PageId) -> Result<Page<'_>, PageError>;

    /// Retrieves a mutable page from the given snapshot.
    fn get_mut(&mut self, snapshot_id: SnapshotId, page_id: PageId) -> Result<PageMut<'_>, PageError>;

    /// Retrieves a mutable clone of a page from the given snapshot.
    fn get_mut_clone(&mut self, snapshot_id: SnapshotId, page_id: PageId) -> Result<PageMut<'_>, PageError>;

    /// Allocates a new page in the given snapshot.
    fn allocate(&mut self, snapshot_id: SnapshotId) -> Result<PageMut<'_>, PageError>;

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
