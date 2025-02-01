use crate::snapshot::SnapshotId;
use crate::page::PageId;

pub const PAGE_SIZE: usize = 4096;
pub const HEADER_SIZE: usize = 8;
pub const PAGE_DATA_SIZE: usize = PAGE_SIZE - HEADER_SIZE;

// Represents a page in the database.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Page<'p> {
    pub id: PageId,
    data: &'p [u8; PAGE_SIZE],
    snapshot_id: SnapshotId,
}

impl<'p> Page<'p> {
    // Creates a new Page with the given id, snapshot id, and data.
    pub fn new(id: PageId, data: &'p [u8; PAGE_SIZE]) -> Self {
        let snapshot_id = u64::from_le_bytes(data[0..8].try_into().unwrap());
        Self { id, snapshot_id, data }
    }

    // Returns the snapshot id of the page.
    pub fn snapshot_id(&self) -> SnapshotId {
        self.snapshot_id
    }

    // Returns the contents of the page without the header
    pub fn contents(&self) -> &'p [u8] {
        &self.data[HEADER_SIZE..]
    }
}

// Represents a mutable handle to a page in the database.
#[derive(Debug, PartialEq, Eq)]
pub struct PageMut<'p> {
    pub id: PageId,
    data: &'p mut [u8; PAGE_SIZE],
    snapshot_id: SnapshotId,
}

impl<'p> PageMut<'p> {
    // Creates a new PageMut with the given id, snapshot id, and data.
    pub fn new(id: PageId, snapshot_id: SnapshotId, data: &'p mut [u8; PAGE_SIZE]) -> Self {
        data[0..8].copy_from_slice(&snapshot_id.to_le_bytes());
        Self { id, snapshot_id, data }
    }

    // Returns the snapshot id of the page.
    pub fn snapshot_id(&self) -> SnapshotId {
        self.snapshot_id
    }

    // Returns the contents of the page without the header
    pub fn contents(&self) -> &[u8] {
        &self.data[HEADER_SIZE..]
    }

    pub fn contents_mut(&mut self) -> &mut [u8] {
        &mut self.data[HEADER_SIZE..]
    }
}
