use crate::{page::Page, snapshot::SnapshotId};
use alloy_primitives::B256;

use super::{
    page::{PageKind, RO, RW},
    PageError, PageId, PageManager, PAGE_DATA_SIZE,
};

const MAX_ORPHANS: usize = 1011;

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

    pub fn root_subtrie_page_id(&self) -> PageId {
        PageId::from_le_bytes(
            self.page.contents()[32..36]
                .try_into()
                .expect("subtrie page id is 4 bytes"),
        )
    }

    pub fn max_page_number(&self) -> PageId {
        PageId::from_le_bytes(
            self.page.contents()[36..40]
                .try_into()
                .expect("max page number is 4 bytes"),
        )
    }

    pub fn get_orphaned_page_ids<T: PageManager>(
        &self,
        page_manager: &T,
    ) -> Result<Vec<PageId>, PageError> {
        // A "slot" can be thought of as a single orphan page_id which is 4 bytes.
        // We start at slot 10 (byte index 40 == 10*4) because the root page contains metadata before the orphan
        // list starts: state_root(32 bytes) + root_subtrie_page_number(4 bytes) + max_page_number(4 bytes)
        let current_slot_index = 10;
        let mut orphan_page_ids = Vec::new();

        self.get_orphaned_page_ids_helper(
            self.page.contents(),
            current_slot_index,
            &mut orphan_page_ids,
            page_manager,
        )?;

        Ok(orphan_page_ids)
    }

    fn get_orphaned_page_ids_helper<T: PageManager>(
        &self,
        page_contents: &[u8],
        mut current_slot_index: usize,
        orphan_page_ids: &mut Vec<PageId>,
        page_manager: &T,
    ) -> Result<(), PageError> {
        let last_slot_index = (page_contents.len() / 4) - 1;

        // Keep reading orphan page ids, across pages, until we encounter an orphan page id
        // that is 0
        loop {
            let current_orphan_page_id_start_index = current_slot_index * 4;
            let orphan_page_id = u32::from_le_bytes(
                page_contents
                    [current_orphan_page_id_start_index..current_orphan_page_id_start_index + 4]
                    .try_into()
                    .expect("orphan page id is 4 bytes"),
            );

            // orphan page id list is 0 terminated
            if orphan_page_id == 0 {
                return Ok(());
            }

            if current_slot_index == last_slot_index {
                // the last slot is a special case that, if non-zero, indicates that the
                // orphan list continues at the page id stored in the last slot.
                let next_page = page_manager.get(self.snapshot_id(), orphan_page_id)?;
                return self.get_orphaned_page_ids_helper(
                    next_page.contents(),
                    0,
                    orphan_page_ids,
                    page_manager,
                );
            }

            orphan_page_ids.push(orphan_page_id);
            current_slot_index = current_slot_index + 1;
        }
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
        let offset = 40 + self.orphan_count * 4;
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

impl<'p> From<RootPage<'p, RW>> for RootPage<'p, RO> {
    fn from(root_page: RootPage<'p, RW>) -> Self {
        Self {
            page: root_page.page.into(),
            orphan_count: root_page.orphan_count,
        }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::page::MmapPageManager;
    use crate::page::PAGE_SIZE;

    #[test]
    fn test_get_orphan_page_ids() {
        /// GIVEN: a root page with orphan ids
        let mut page_manager = MmapPageManager::new_anon(20, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        let mut root_page = RootPage::new(page, B256::default());
        let my_orphan_page_ids: &[PageId] = &[2, 3, 4, 5, 6, 7, 8, 9, 10];
        for i in my_orphan_page_ids {
            root_page.add_orphaned_page_id(*i).unwrap();
        }

        /// WHEN: the list of orphan ids are requested
        let root_page_ro: RootPage<RO> = root_page.into();
        let orphan_page_ids = root_page_ro.get_orphaned_page_ids(&page_manager).unwrap();

        /// THEN: the returned list of orphan page ids should match the original list
        assert_eq!(my_orphan_page_ids.to_vec(), orphan_page_ids);
    }

    #[test]
    fn test_get_empty_orphan_page_ids() {
        /// GIVEN: a root page with no orphan ids
        let mut page_manager = MmapPageManager::new_anon(20, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        let mut root_page = RootPage::new(page, B256::default());

        /// WHEN: the list of orphan ids are requested
        let root_page_ro: RootPage<RO> = root_page.into();
        let orphan_page_ids = root_page_ro.get_orphaned_page_ids(&page_manager).unwrap();

        /// THEN: the returned list of orphan page ids should be empty
        assert_eq!(orphan_page_ids.len(), 0);
    }

    #[test]
    fn test_2_page_orphan_page_ids() {
        /// GIVEN: a root page with a list of orphan page ids spanning 2 pages
        let mut page_manager = MmapPageManager::new_anon(20, 0).unwrap();
        let mut page1 = page_manager.allocate(42).unwrap();
        let mut page2 = page_manager.allocate(42).unwrap();
        let mut my_orphan_page_ids = Vec::new();

        // add the id of page2 to the last slot (4 bytes) of root page 1.
        // this will indicate that the orphan page list continues into page2
        let data = page1.contents_mut();
        let size = data.len();
        data[size - 4..].copy_from_slice(&page2.page_id().to_le_bytes());

        let mut root_page = RootPage::new(page1, B256::default());
        // we should be able to store 1011 orphan page ids in a root page.
        // the last 4 bytes of the root page will be the next page id containing
        // the remainder of the list of orphan page ids
        for i in 0..1011 {
            root_page.add_orphaned_page_id(i + 1).unwrap();
            my_orphan_page_ids.push(i + 1);
        }

        // add more orphan page_ids to page 2
        let page2_data = page2.contents_mut();
        for i in 1011..2011 {
            let start = (i - 1011) * 4;
            let end = start + 4;
            page2_data[start..end].copy_from_slice(&(i as u32).to_le_bytes());
            my_orphan_page_ids.push(i as u32);
        }

        /// WHEN: the list of orphan ids are requested
        let root_page_ro: RootPage<RO> = root_page.into();
        let orphan_page_ids = root_page_ro.get_orphaned_page_ids(&page_manager).unwrap();

        /// THEN: the returned list of orphan page ids should match the original list
        assert_eq!(my_orphan_page_ids, orphan_page_ids);
    }
}
