use crate::{page::PageId, snapshot::SnapshotId};
use std::{fmt, mem, ops::Deref};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

// In order to support zero-copy access to the on-disk data, and to ensure the same serialization
// format on all supported platforms, we must stick to one endianness. In practice, this ensures
// that one can copy the database file from one machine to another, and the database software will
// be able to use it reliably.
#[cfg(not(target_endian = "little"))]
compile_error!("This code only supports little-endian platforms");

pub const PAGE_SIZE: usize = 4096;
pub const HEADER_SIZE: usize = 8;
pub const PAGE_DATA_SIZE: usize = PAGE_SIZE - HEADER_SIZE;

#[repr(C)]
#[derive(FromBytes, IntoBytes, Immutable, KnownLayout)]
struct PageHeader {
    snapshot_id: SnapshotId,
}

#[repr(C, align(4096))]
#[derive(FromBytes, IntoBytes, Immutable, KnownLayout)]
struct PageData {
    header: PageHeader,
    contents: [u8; PAGE_DATA_SIZE],
}

#[derive(Copy, Clone)]
pub struct Page<'p> {
    id: PageId,
    data: &'p PageData,
}

pub struct PageMut<'p> {
    #[allow(dead_code)]
    id: PageId,
    data: &'p mut PageData,
}

// Compile-time assertion to verify that `PageData` and `PageHeader` have the expected size,
// alignment, and internal layout.
const _: () = {
    use std::mem::{align_of, offset_of, size_of};

    assert!(size_of::<PageData>() == PAGE_SIZE);
    assert!(align_of::<PageData>() == PAGE_SIZE);

    assert!(size_of::<PageHeader>() == HEADER_SIZE);
    assert!(align_of::<PageHeader>() == HEADER_SIZE);

    assert!(offset_of!(PageData, header) == 0);
    assert!(offset_of!(PageData, contents) == HEADER_SIZE);
};

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
};

fn fmt_page(name: &str, p: &Page<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct(name)
        .field("id", &p.id())
        .field("data", &"[...]")
        .field("snapshot_id", &p.snapshot_id())
        .finish()
}

impl<'p> Page<'p> {
    /// Constructs a new immutable page for reading.
    ///
    /// # Panics
    ///
    /// If `data` is not aligned to the page size.
    pub fn new(id: PageId, data: &'p [u8; PAGE_SIZE]) -> Self {
        let data = PageData::ref_from_bytes(data).expect("data must be properly aligned");
        Self { id, data }
    }

    pub fn id(&self) -> PageId {
        self.id
    }

    /// Returns the snapshot id of the page.
    pub fn snapshot_id(&self) -> SnapshotId {
        self.data.header.snapshot_id
    }

    /// Returns the contents of the page without the header
    pub fn contents(&self) -> &[u8] {
        &self.data.contents
    }
}

impl fmt::Debug for Page<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_page("Page", self, f)
    }
}

impl<'p> PageMut<'p> {
    /// Constructs a new mutable page for reading and writing.
    ///
    /// # Panics
    ///
    /// If `data` is not aligned to the page size.
    pub fn new(id: PageId, data: &'p mut [u8; PAGE_SIZE]) -> Self {
        let data = PageData::mut_from_bytes(data).expect("data must be properly aligned");
        Self { id, data }
    }

    /// Creates a new RW Page with the given id, snapshot id, and data.
    pub fn with_snapshot(
        id: PageId,
        snapshot_id: SnapshotId,
        data: &'p mut [u8; PAGE_SIZE],
    ) -> Self {
        let mut page = Self::new(id, data);
        page.set_snapshot_id(snapshot_id);
        page
    }

    pub fn set_snapshot_id(&mut self, snapshot_id: SnapshotId) {
        self.data.header.snapshot_id = snapshot_id;
    }

    /// Returns a mutable reference to the contents of the page without the header
    pub fn contents_mut(&mut self) -> &mut [u8] {
        &mut self.data.contents
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

    #[repr(align(4096))]
    struct DataArray([u8; PAGE_SIZE]);

    #[test]
    fn test_ref_new() {
        let id = 42;
        let data = DataArray([0; PAGE_SIZE]);

        let page = Page::new(id, &data.0);

        assert_eq!(page.id(), 42);
        assert_eq!(page.snapshot_id(), 0);
        assert_eq!(page.contents(), [0u8; PAGE_DATA_SIZE]);
    }

    #[test]
    fn test_mut_new() {
        let id = 42;
        let mut data = DataArray([0; PAGE_SIZE]);

        let page_mut = PageMut::new(id, &mut data.0);

        assert_eq!(page_mut.id(), 42);
        assert_eq!(page_mut.snapshot_id(), 0);
        assert_eq!(page_mut.contents(), [0u8; PAGE_DATA_SIZE]);
    }

    #[test]
    fn test_mut_with_snapshot() {
        let id = 42;
        let snapshot = 1337;
        let mut data = DataArray([0; PAGE_SIZE]);

        let page_mut = PageMut::with_snapshot(id, snapshot, &mut data.0);

        assert_eq!(page_mut.id(), 42);
        assert_eq!(page_mut.snapshot_id(), 1337);
        assert_eq!(page_mut.contents(), [0u8; PAGE_DATA_SIZE]);
    }
}
