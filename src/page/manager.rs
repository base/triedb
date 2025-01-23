use std::fmt::Debug;

/// currently we use 4 bytes for page ids, which implies a maximum of 16TB of data.
pub type PageId = u32;

/// TODO: potentially use a a more sophisticated snapshotting mechanism that requires a Snapshot struct to carry more context.
pub type SnapshotId = u64;

/// Represents various errors that might arise from page operations.
#[derive(Debug)]
pub enum PageError {
    PageNotFound(PageId),
    IO(std::io::Error),
    // TODO: add more errors here for other cases.
}

/// Core trait that manages pages in trie db.
pub trait PageManager: Debug {
    /// Retrieves a page from the given snapshot.
    fn get(&self, snapshot_id: SnapshotId, page_id: PageId) -> Result<Page, PageError>;

    /// Allocates a new page in the given snapshot.
    fn allocate(&mut self, snapshot_id: SnapshotId) -> Result<PageId, PageError>;

    /// Merges two pages into a new page.
    fn merge(
        &mut self,
        snapshot_id: SnapshotId,
        page_a: PageId,
        page_b: PageId,
        page_out: PageId,
    ) -> Result<(), PageError>;

    /// Splits a page into two new pages.
    fn split(
        &mut self,
        snapshot_id: SnapshotId,
        page_id: PageId,
    ) -> Result<(PageId, PageId), PageError>;

    /// Writes data to a page.
    fn write(
        &mut self,
        snapshot_id: SnapshotId,
        page_id: PageId,
        data: &[u8],
    ) -> Result<(), PageError>;

    /// Commits pages associated with a snapshot to durable storage.
    fn commit(&mut self, snapshot_id: SnapshotId) -> Result<(), PageError>;
}
