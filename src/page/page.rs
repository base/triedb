use sealed::sealed;

use crate::{page::PageId, snapshot::SnapshotId};

pub const PAGE_SIZE: usize = 4096;
pub const HEADER_SIZE: usize = 8;
pub const PAGE_DATA_SIZE: usize = PAGE_SIZE - HEADER_SIZE;

#[sealed]
pub trait PageKind {}

#[derive(Debug)]
pub struct RO {}

#[sealed]
impl PageKind for RO {}

#[derive(Debug)]
pub struct RW {}

#[sealed]
impl PageKind for RW {}

#[derive(Debug)]
pub struct Page<'p, P: PageKind> {
    id: PageId,
    data: &'p mut [u8; PAGE_SIZE],
    snapshot_id: SnapshotId,
    _marker: std::marker::PhantomData<P>,
}

impl<P: PageKind> Page<'_, P> {
    pub fn page_id(&self) -> PageId {
        self.id
    }

    // Returns the snapshot id of the page.
    pub fn snapshot_id(&self) -> SnapshotId {
        self.snapshot_id
    }

    // Returns the contents of the page without the header
    pub fn contents(&self) -> &[u8] {
        &self.data[HEADER_SIZE..]
    }
}

impl<'p> Page<'p, RO> {
    pub fn new_ro(id: PageId, data: &'p mut [u8; PAGE_SIZE]) -> Self {
        let snapshot_id = u64::from_le_bytes(data[0..8].try_into().unwrap());
        Self {
            id,
            snapshot_id,
            data,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'p> Page<'p, RW> {
    pub fn new_rw(id: PageId, data: &'p mut [u8; PAGE_SIZE]) -> Self {
        let snapshot_id = u64::from_le_bytes(data[0..8].try_into().unwrap());
        Self {
            id,
            snapshot_id,
            data,
            _marker: std::marker::PhantomData,
        }
    }

    // Creates a new RW Page with the given id, snapshot id, and data.
    pub fn new_rw_with_snapshot(
        id: PageId,
        snapshot_id: SnapshotId,
        data: &'p mut [u8; PAGE_SIZE],
    ) -> Self {
        data[0..8].copy_from_slice(&snapshot_id.to_le_bytes());
        Self {
            id,
            snapshot_id,
            data,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn set_snapshot_id(&mut self, snapshot_id: SnapshotId) {
        self.snapshot_id = snapshot_id;
        self.data[0..8].copy_from_slice(&snapshot_id.to_le_bytes());
    }

    // Returns a mutable reference to the contents of the page without the header
    pub fn contents_mut(&mut self) -> &mut [u8] {
        &mut self.data[HEADER_SIZE..]
    }
}

impl<'p> From<Page<'p, RW>> for Page<'p, RO> {
    fn from(page: Page<'p, RW>) -> Self {
        Self::new_ro(page.id, page.data)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_page_mut_clone() {
        let page_id = 42;
        let snapshot_id = 1337;

        let mut data = [0; PAGE_SIZE];
        let mut page_mut = Page::new_rw_with_snapshot(page_id, snapshot_id, &mut data);
        assert_eq!(page_mut.page_id(), page_id);
        assert_eq!(page_mut.snapshot_id(), snapshot_id);
        assert_eq!(page_mut.contents()[0], 0);

        page_mut.contents_mut()[0] = 1;
        assert_eq!(page_mut.contents_mut()[0], 1);
        assert_eq!(page_mut.contents()[0], 1);

        let page = Page::<'_, RO>::from(page_mut);
        assert_eq!(page.page_id(), page_id);
        assert_eq!(page.snapshot_id(), snapshot_id);
        assert_eq!(page.contents()[0], 1);

        assert_eq!(data[HEADER_SIZE], 1);
    }
}
