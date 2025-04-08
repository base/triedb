use super::{PageError, PageId};
use crate::{
    page::{page::PageHeader, Page, PageMut},
    snapshot::SnapshotId,
};
use std::{mem, num::NonZero, ops::Deref};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

#[repr(C, align(4096))]
#[derive(FromBytes, IntoBytes, Immutable, KnownLayout, Debug)]
pub(super) struct OrphanListPageData {
    pub(super) header: PageHeader,
    pub(super) orphaned_page_ids: [Option<NonZero<PageId>>; 1021],
    pub(super) next: Option<NonZero<PageId>>,
}

#[derive(Copy, Clone, Debug)]
pub struct OrphanListPage<'p> {
    pub(super) id: PageId,
    pub(super) data: &'p OrphanListPageData,
}

#[derive(Debug)]
pub struct OrphanListPageMut<'p> {
    pub(super) id: PageId,
    pub(super) data: &'p mut OrphanListPageData,
}

// Compile-time assertion to verify that `OrphanListPage` and `OrphanListPageMut` have the same
// layout and internal structure (and consequently that `OrphanListPageMut` can be safely
// transmuted to `OrphanListPage`).
const _: () = {
    use std::{alloc::Layout, mem::offset_of};

    let ref_layout = Layout::new::<OrphanListPage<'_>>();
    let mut_layout = Layout::new::<OrphanListPageMut<'_>>();
    assert!(ref_layout.size() == mut_layout.size());
    assert!(ref_layout.align() == mut_layout.align());

    assert!(offset_of!(OrphanListPage<'_>, id) == offset_of!(OrphanListPageMut<'_>, id));
    assert!(offset_of!(OrphanListPage<'_>, data) == offset_of!(OrphanListPageMut<'_>, data));
};

impl OrphanListPage<'_> {
    pub fn id(&self) -> PageId {
        self.id
    }

    pub fn snapshot_id(&self) -> SnapshotId {
        self.data.header.snapshot_id
    }

    pub fn orphaned_page_ids(&self) -> impl Iterator<Item = PageId> + use<'_> {
        self.data.orphaned_page_ids.iter().filter_map(|item| item.map(NonZero::get))
    }

    pub fn next(&self) -> Option<PageId> {
        self.data.next.map(NonZero::get)
    }
}

impl OrphanListPageMut<'_> {}

impl<'a> TryFrom<Page<'a>> for OrphanListPage<'a> {
    type Error = PageError;

    fn try_from(page: Page<'a>) -> Result<Self, Self::Error> {
        let Page { id, data } = page;
        if id < 2 {
            return Err(PageError::InvalidPageId(id));
        }

        let data = zerocopy::transmute_ref!(data);
        Ok(Self { id, data })
    }
}

impl<'a> TryFrom<PageMut<'a>> for OrphanListPageMut<'a> {
    type Error = PageError;

    fn try_from(page: PageMut<'a>) -> Result<Self, Self::Error> {
        let PageMut { id, data } = page;
        if id < 2 {
            return Err(PageError::InvalidPageId(id));
        }

        let data = zerocopy::transmute_mut!(data);
        Ok(Self { id, data })
    }
}

impl<'a> From<OrphanListPage<'a>> for Page<'a> {
    fn from(page: OrphanListPage<'a>) -> Self {
        let OrphanListPage { id, data } = page;
        let data = zerocopy::transmute_ref!(data);
        Self { id, data }
    }
}

impl<'a> From<OrphanListPageMut<'a>> for PageMut<'a> {
    fn from(page: OrphanListPageMut<'a>) -> Self {
        let OrphanListPageMut { id, data } = page;
        let data = zerocopy::transmute_mut!(data);
        Self { id, data }
    }
}

impl<'a> Deref for OrphanListPageMut<'a> {
    type Target = OrphanListPage<'a>;

    fn deref(&self) -> &Self::Target {
        // SAFETY: `OrphanListPage` and `OrphanListPageMut` have the same layout and
        // representation. This transmutation has the only effect of downcasting a mutable
        // reference to an immutable reference, which is safe.
        unsafe { mem::transmute(self) }
    }
}
