use crate::{page::PageId, snapshot::SnapshotId};
use std::{fmt, mem, ops::Deref};

pub const PAGE_SIZE: usize = 4096;
pub const HEADER_SIZE: usize = 8;
pub const PAGE_DATA_SIZE: usize = PAGE_SIZE - HEADER_SIZE;

#[derive(Copy, Clone)]
pub struct Page<'p> {
    id: PageId,
    data: &'p [u8; PAGE_SIZE],
    snapshot_id: SnapshotId,
}

pub struct PageMut<'p> {
    #[allow(dead_code)]
    id: PageId,
    data: &'p mut [u8; PAGE_SIZE],
    snapshot_id: SnapshotId,
}

// Compile-time assertion to verify that `Page` and `PageMut` have the same layout and internal
// structure (and consequently that `PageMut` can be safely transmuted to `Page`).
const _: () = {
    use std::{alloc::Layout, mem::offset_of};

    let ref_layout = Layout::new::<Page<'_>>();
    let mut_layout = Layout::new::<PageMut<'_>>();
    assert!(ref_layout.size() == mut_layout.size());
    assert!(ref_layout.align() == mut_layout.align());

    assert!(offset_of!(Page<'_>, id) == offset_of!(PageMut<'_>, id));
    assert!(offset_of!(Page<'_>, data) == offset_of!(PageMut<'_>, data));
    assert!(offset_of!(Page<'_>, snapshot_id) == offset_of!(PageMut<'_>, snapshot_id));
};

fn fmt_page(name: &str, p: &Page<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct(name)
        .field("id", &p.id())
        .field("data", &"[...]")
        .field("snapshot_id", &p.snapshot_id())
        .finish()
}

impl<'p> Page<'p> {
    pub fn new(id: PageId, data: &'p [u8; PAGE_SIZE]) -> Self {
        let snapshot_id = u64::from_le_bytes(data[0..8].try_into().unwrap());
        Self { id, snapshot_id, data }
    }

    pub fn id(&self) -> PageId {
        self.id
    }

    /// Returns the snapshot id of the page.
    pub fn snapshot_id(&self) -> SnapshotId {
        self.snapshot_id
    }

    /// Returns the contents of the page without the header
    pub fn contents(&self) -> &[u8] {
        &self.data[HEADER_SIZE..]
    }
}

impl fmt::Debug for Page<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_page("Page", self, f)
    }
}

impl<'p> PageMut<'p> {
    pub fn new(id: PageId, data: &'p mut [u8; PAGE_SIZE]) -> Self {
        let snapshot_id = u64::from_le_bytes(data[0..8].try_into().unwrap());
        Self { id, snapshot_id, data }
    }

    /// Creates a new RW Page with the given id, snapshot id, and data.
    pub fn with_snapshot(
        id: PageId,
        snapshot_id: SnapshotId,
        data: &'p mut [u8; PAGE_SIZE],
    ) -> Self {
        data[0..8].copy_from_slice(&snapshot_id.to_le_bytes());
        Self { id, snapshot_id, data }
    }

    pub fn set_snapshot_id(&mut self, snapshot_id: SnapshotId) {
        self.snapshot_id = snapshot_id;
        self.data[0..8].copy_from_slice(&snapshot_id.to_le_bytes());
    }

    /// Returns a mutable reference to the contents of the page without the header
    pub fn contents_mut(&mut self) -> &mut [u8] {
        &mut self.data[HEADER_SIZE..]
    }
}

impl<'p> Deref for PageMut<'p> {
    type Target = Page<'p>;

    fn deref(&self) -> &Page<'p> {
        // SAFETY: `Page` and `PageMut` have the same layout and representation. This transmutation
        // has the only effect of downcasting a mutable reference to an immutable reference, which
        // is safe.
        unsafe { mem::transmute(self) }
    }
}

impl fmt::Debug for PageMut<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_page("PageMut", self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ref_new() {
        let id = 42;
        let mut data = [0; PAGE_SIZE];

        let page = Page::new(id, &mut data);

        assert_eq!(page.id(), 42);
        assert_eq!(page.snapshot_id(), 0);
        assert_eq!(page.contents(), [0u8; PAGE_DATA_SIZE]);
    }

    #[test]
    fn test_mut_new() {
        let id = 42;
        let mut data = [0; PAGE_SIZE];

        let page_mut = PageMut::new(id, &mut data);

        assert_eq!(page_mut.id(), 42);
        assert_eq!(page_mut.snapshot_id(), 0);
        assert_eq!(page_mut.contents(), [0u8; PAGE_DATA_SIZE]);
    }

    #[test]
    fn test_mut_with_snapshot() {
        let id = 42;
        let snapshot = 1337;
        let mut data = [0; PAGE_SIZE];

        let page_mut = PageMut::with_snapshot(id, snapshot, &mut data);

        assert_eq!(page_mut.id(), 42);
        assert_eq!(page_mut.snapshot_id(), 1337);
        assert_eq!(page_mut.contents(), [0u8; PAGE_DATA_SIZE]);
    }
}
