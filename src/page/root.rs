use crate::{page::{Page, PageMut}, snapshot::SnapshotId};
use alloy_primitives::B256;

use super::{PageError, PageId, ReadablePage, WritablePage};
pub struct RootPage<'p> {
    page: Page<'p>,
}

impl<'p> RootPage<'p> {
    pub fn new(mut page_mut: PageMut<'p>, state_root: B256) -> Self {
        let contents = page_mut.contents_mut();
        contents[0..32].copy_from_slice(state_root.as_slice());
        Self { page: page_mut.into() }
    }

    pub fn state_root(&self) -> B256 {
        B256::from_slice(&self.page.contents()[0..32])
    }

    pub fn id(&self) -> PageId {
        self.page.page_id()
    }

    pub fn snapshot_id(&self) -> SnapshotId {
        self.page.snapshot_id()
    }
}

impl<'p> From<RootPage<'p>> for Page<'p> {
    fn from(root_page: RootPage<'p>) -> Self {
        root_page.page
    }
}

impl<'p> TryFrom<Page<'p>> for RootPage<'p> {
    type Error = PageError;

    fn try_from(page: Page<'p>) -> Result<Self, Self::Error> {
        if page.page_id() > 1 {
            return Err(PageError::InvalidRootPage(page.page_id()));
        }
        Ok(Self { page })
    }
}