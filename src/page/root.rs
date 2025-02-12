use crate::{page::Page, snapshot::SnapshotId};
use alloy_primitives::B256;

use super::{
    page::{PageKind, RO, RW},
    PageError, PageId,
};

const MAX_ORPHANS: usize = 1000;

pub struct RootPage<'p, P: PageKind> {
    page: Page<'p, P>,
    orphan_count: usize,
}

impl<'p, P: PageKind> RootPage<'p, P> {
    pub fn page_id(&self) -> PageId {
        self.page.page_id()
    }

    pub fn snapshot_id(&self) -> SnapshotId {
        self.page.snapshot_id()
    }

    pub fn state_root(&self) -> B256 {
        B256::from_slice(&self.page.contents()[0..32])
    }
}

impl<'p> RootPage<'p, RW> {
    pub fn new(mut page_mut: Page<'p, RW>, state_root: B256) -> Self {
        let contents = page_mut.contents_mut();
        contents[0..32].copy_from_slice(state_root.as_slice());
        Self {
            page: page_mut,
            orphan_count: 0,
        }
    }

    pub fn add_orphaned_page_id(&mut self, page_id: PageId) -> Result<(), ()> {
        // TODO: allow this to spill over to another page
        if self.orphan_count >= MAX_ORPHANS {
            return Err(());
        }
        let offset = 32 + self.orphan_count * 4;
        self.page.contents_mut()[offset..offset + 4].copy_from_slice(&page_id.to_le_bytes());
        self.orphan_count += 1;
        Ok(())
    }
}

impl<'p> From<RootPage<'p, RW>> for Page<'p, RO> {
    fn from(root_page: RootPage<'p, RW>) -> Self {
        root_page.page.into()
    }
}

impl<'p, P: PageKind> TryFrom<Page<'p, P>> for RootPage<'p, P> {
    type Error = PageError;

    fn try_from(page: Page<'p, P>) -> Result<Self, Self::Error> {
        if page.page_id() > 1 {
            return Err(PageError::InvalidRootPage(page.page_id()));
        }
        // TODO: read the orphans from the page contents
        Ok(Self {
            page,
            orphan_count: 0,
        })
    }
}
