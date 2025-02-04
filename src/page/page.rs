use crate::snapshot::SnapshotId;
use crate::page::PageId;

pub const PAGE_SIZE: usize = 4096;
pub const HEADER_SIZE: usize = 8;
pub const PAGE_DATA_SIZE: usize = PAGE_SIZE - HEADER_SIZE;

pub trait ReadablePage<'p> {
    fn page_id(&self) -> PageId;
    fn snapshot_id(&self) -> SnapshotId;
    fn contents(&'p self) -> &'p [u8];
}

pub trait WritablePage<'p> {
    fn contents_mut(&mut self) -> &mut [u8];
}

// Represents a page in the database.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Page<'p> {
    id: PageId,
    data: &'p [u8; PAGE_SIZE],
    snapshot_id: SnapshotId,
}

impl<'p> Page<'p> {
    // Creates a new Page with the given id, snapshot id, and data.
    pub fn new(id: PageId, data: &'p [u8; PAGE_SIZE]) -> Self {
        let snapshot_id = u64::from_le_bytes(data[0..8].try_into().unwrap());
        Self { id, snapshot_id, data }
    }
}

impl<'p> ReadablePage<'p> for Page<'p> {
    fn page_id(&self) -> PageId {
        self.id
    }

    // Returns the snapshot id of the page.
    fn snapshot_id(&self) -> SnapshotId {
        self.snapshot_id
    }

    // Returns the contents of the page without the header
    fn contents(&'p self) -> &'p [u8] {
        &self.data[HEADER_SIZE..]
    }
}

// Represents a mutable handle to a page in the database.
#[derive(Debug, PartialEq, Eq)]
pub struct PageMut<'p> {
    id: PageId,
    data: &'p mut [u8; PAGE_SIZE],
    snapshot_id: SnapshotId,
}

impl<'p> PageMut<'p> {
    // Creates a new PageMut with the given id, snapshot id, and data.
    pub fn new(id: PageId, snapshot_id: SnapshotId, data: &'p mut [u8; PAGE_SIZE]) -> Self {
        data[0..8].copy_from_slice(&snapshot_id.to_le_bytes());
        Self { id, snapshot_id, data }
    }
}

impl<'p> ReadablePage<'p> for PageMut<'p> {
    fn page_id(&self) -> PageId {
        self.id
    }

    // Returns the snapshot id of the page.
    fn snapshot_id(&self) -> SnapshotId {
        self.snapshot_id
    }

    // Returns the contents of the page without the header
    fn contents(&'p self) -> &'p [u8] {
        &self.data[HEADER_SIZE..]
    }
}

impl<'p> WritablePage<'p> for PageMut<'p> {
    // Returns a mutable reference to the contents of the page without the header
    fn contents_mut(&mut self) -> &mut [u8] {
        &mut self.data[HEADER_SIZE..]
    }
}

impl<'p> From<PageMut<'p>> for Page<'p> {
    fn from(page: PageMut<'p>) -> Self {
        Self::new(page.id, page.data)
    }
}
