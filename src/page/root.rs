use super::{PageError, PageId, PageManager};
use crate::{
    page::{page::PageHeader, OrphanListPage, OrphanListPageMut, Page, PageMut},
    snapshot::SnapshotId,
};
use alloy_primitives::B256;
use std::{iter, mem, num::NonZero, ops::Deref};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

#[repr(C, align(4096))]
#[derive(FromBytes, IntoBytes, Immutable, KnownLayout, Debug)]
pub(super) struct RootPageData {
    pub(super) header: PageHeader,
    pub(super) state_root: [u8; 32],
    pub(super) root_subtrie_page_id: PageId,
    pub(super) max_page_number: PageId,
    pub(super) orphaned_page_ids: [Option<NonZero<PageId>>; 1011],
    pub(super) next: Option<NonZero<PageId>>,
}

#[derive(Copy, Clone, Debug)]
pub struct RootPage<'p> {
    pub(super) id: PageId,
    pub(super) data: &'p RootPageData,
}

#[derive(Debug)]
pub struct RootPageMut<'p> {
    pub(super) id: PageId,
    pub(super) data: &'p mut RootPageData,
}

// Compile-time assertion to verify that `RootPage` and `RootPageMut` have the same layout and
// internal structure (and consequently that `RootPageMut` can be safely transmuted to `RootPage`).
const _: () = {
    use std::{alloc::Layout, mem::offset_of};

    let ref_layout = Layout::new::<RootPage<'_>>();
    let mut_layout = Layout::new::<RootPageMut<'_>>();
    assert!(ref_layout.size() == mut_layout.size());
    assert!(ref_layout.align() == mut_layout.align());

    assert!(offset_of!(RootPage<'_>, id) == offset_of!(RootPageMut<'_>, id));
    assert!(offset_of!(RootPage<'_>, data) == offset_of!(RootPageMut<'_>, data));
};

impl RootPage<'_> {
    pub fn id(&self) -> PageId {
        self.id
    }

    pub fn snapshot_id(&self) -> SnapshotId {
        self.data.header.snapshot_id
    }

    pub fn state_root(&self) -> B256 {
        B256::from(self.data.state_root)
    }

    pub fn root_subtrie_page_id(&self) -> PageId {
        self.data.root_subtrie_page_id
    }

    pub fn max_page_number(&self) -> PageId {
        self.data.max_page_number
    }

    pub fn get_orphaned_page_ids(
        &self,
        page_manager: &PageManager,
    ) -> Result<Vec<PageId>, PageError> {
        let mut result = self
            .data
            .orphaned_page_ids
            .iter()
            .filter_map(|item| item.map(NonZero::get))
            .collect::<Vec<PageId>>();

        let mut next = self.data.next.map(NonZero::get);
        while let Some(next_page_id) = next {
            assert!(next_page_id >= 2, "orphan continuation page cannot be a root page");
            let page = page_manager
                .get(self.snapshot_id(), next_page_id)
                .and_then(OrphanListPage::try_from)?;
            result.extend(page.orphaned_page_ids());
            next = page.next();
        }

        Ok(result)
    }
}

impl RootPageMut<'_> {
    pub fn set_state_root(&mut self, state_root: B256) {
        self.data.state_root = state_root.into();
    }

    pub fn set_root_subtrie_page_id(&mut self, page_id: PageId) {
        self.data.root_subtrie_page_id = page_id;
    }

    pub fn set_max_page_number(&mut self, page_id: PageId) {
        self.data.max_page_number = page_id;
    }

    pub fn set_orphaned_page_ids<'a>(
        &mut self,
        new_orphan_page_ids: impl IntoIterator<Item = &'a PageId>,
        page_manager: &mut PageManager,
    ) -> Result<(), PageError> {
        let snapshot_id = self.snapshot_id();
        let mut new_orphan_page_ids = new_orphan_page_ids.into_iter().copied().peekable();

        // Place the orphan page IDs in this root first.
        for (slot, page_id) in self
            .data
            .orphaned_page_ids
            .iter_mut()
            .zip((&mut new_orphan_page_ids).chain(iter::repeat(0)))
        {
            *slot = NonZero::new(page_id);
        }

        let mut current_page_id = self.id();
        let mut next_page_pointer = &mut self.data.next;

        // If not all orphan page IDs could fit in the root page, use additional orphan list pages.
        while new_orphan_page_ids.peek().is_some() {
            let orphan_list_page = if let Some(next_page_id) = next_page_pointer {
                // Reuse the orphan list page that was previously used.
                page_manager.get_mut(snapshot_id, next_page_id.get())?
            } else if current_page_id < 255 {
                // Pages from 2 to 255 are reserved for orphan list pages, so use one of that if
                // possible.
                //
                // TODO: This is currently unsafe and unsound, as this may overwrite a page that is
                // still referenced by the other root page.
                let next_page_id = (current_page_id + 1).max(2);
                page_manager.get_mut(snapshot_id, next_page_id)?
            } else {
                // Not enough pages in the range 2..255; need to allocate a new one.
                //
                // TODO: This can leak pages, because if this page is no longer needed in the
                // future, it won't be tracked by the orphan manager.
                page_manager.allocate(snapshot_id)?
            };

            current_page_id = orphan_list_page.id();
            debug_assert!(current_page_id >= 2);

            // Place the next chunk of orphan page IDs in this page.
            let orphan_list_page = OrphanListPageMut::try_from(orphan_list_page)?;
            for (slot, page_id) in orphan_list_page
                .data
                .orphaned_page_ids
                .iter_mut()
                .zip((&mut new_orphan_page_ids).chain(iter::repeat(0)))
            {
                *slot = NonZero::new(page_id);
            }

            // Connect this page to the previous one.
            *next_page_pointer = NonZero::new(current_page_id);
            next_page_pointer = &mut orphan_list_page.data.next;
        }

        *next_page_pointer = None;
        Ok(())
    }
}

impl<'a> TryFrom<Page<'a>> for RootPage<'a> {
    type Error = PageError;

    fn try_from(page: Page<'a>) -> Result<Self, Self::Error> {
        let Page { id, data } = page;
        if id > 1 {
            return Err(PageError::InvalidPageId(id));
        }

        let data = zerocopy::transmute_ref!(data);
        Ok(Self { id, data })
    }
}

impl<'a> TryFrom<PageMut<'a>> for RootPageMut<'a> {
    type Error = PageError;

    fn try_from(page: PageMut<'a>) -> Result<Self, Self::Error> {
        let PageMut { id, data } = page;
        if id > 1 {
            return Err(PageError::InvalidPageId(id));
        }

        let data = zerocopy::transmute_mut!(data);
        Ok(Self { id, data })
    }
}

impl<'a> From<RootPage<'a>> for Page<'a> {
    fn from(page: RootPage<'a>) -> Self {
        let RootPage { id, data } = page;
        let data = zerocopy::transmute_ref!(data);
        Self { id, data }
    }
}

impl<'a> From<RootPageMut<'a>> for PageMut<'a> {
    fn from(page: RootPageMut<'a>) -> Self {
        let RootPageMut { id, data } = page;
        let data = zerocopy::transmute_mut!(data);
        Self { id, data }
    }
}

impl<'a> Deref for RootPageMut<'a> {
    type Target = RootPage<'a>;

    fn deref(&self) -> &Self::Target {
        // SAFETY: `Page` and `PageMut` have the same layout and representation. This transmutation
        // has the only effect of downcasting a mutable reference to an immutable reference, which
        // is safe.
        unsafe { mem::transmute(self) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAX_ORPHANS: usize = 1011;

    #[test]
    fn test_add_get_orphan_page_ids() {
        // GIVEN: a root page with orphan ids
        let mut page_manager = PageManager::new_anon(20, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        let mut root_page = RootPageMut::try_from(page).unwrap();
        let my_orphan_page_ids = [2, 3, 4, 5, 6, 7, 8, 9, 10];
        root_page.set_orphaned_page_ids(&my_orphan_page_ids, &mut page_manager).unwrap();

        // WHEN: the list of orphan ids are requested
        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();

        // THEN: the returned list of orphan page ids should match the original list
        assert_eq!(&my_orphan_page_ids[..], &orphan_page_ids);
    }

    #[test]
    fn test_get_empty_orphan_page_ids() {
        // GIVEN: a root page with no orphan ids
        let mut page_manager = PageManager::new_anon(20, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        let root_page = RootPageMut::try_from(page).unwrap();

        // WHEN: the list of orphan ids are requested
        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();

        // THEN: the returned list of orphan page ids should be empty
        assert_eq!(orphan_page_ids.len(), 0);
    }

    #[test]
    fn test_2_page_orphan_page_ids() {
        // GIVEN: a root page with a list of orphan page ids spanning into page 2
        let mut page_manager = PageManager::new_anon(20, 0).unwrap();
        let page0 = page_manager.allocate(42).unwrap();
        let _page1 = page_manager.allocate(42).unwrap();
        let mut page2 = page_manager.allocate(42).unwrap();
        let mut my_orphan_page_ids: Vec<PageId> = Vec::new();

        let mut root_page = RootPageMut::try_from(page0).unwrap();
        // we should be able to store MAX_ORPHANS orphan page ids in a root page.
        // the last 4 bytes of the root page will be the next page id containing
        // the remainder of the list of orphan page ids
        let orphan_page_ids = (1..MAX_ORPHANS as PageId + 1).collect::<Vec<PageId>>();
        root_page.set_orphaned_page_ids(&orphan_page_ids, &mut page_manager).unwrap();
        for i in orphan_page_ids {
            my_orphan_page_ids.push(i);
        }

        // add the id of page2 to the last slot (4 bytes) of root page 0.
        // this will indicate that the orphan page list continues into page2
        let mut page0 = page_manager.get_mut(42, 0).unwrap();
        let data = page0.contents_mut();
        let size = data.len();
        data[size - 4..].copy_from_slice(&page2.id().to_le_bytes());

        // add more orphan page_ids to page 2
        let page2_data = page2.contents_mut();
        for i in MAX_ORPHANS..2011 {
            let start = (i - MAX_ORPHANS) * 4;
            let end = start + 4;
            page2_data[start..end].copy_from_slice(&(i as u32).to_le_bytes());
            my_orphan_page_ids.push(i as u32);
        }

        // WHEN: the list of orphan ids are requested
        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();

        // THEN: the returned list of orphan page ids should match the original list
        assert_eq!(my_orphan_page_ids, orphan_page_ids);
    }

    #[test]
    fn test_root_0_doesnt_spill_into_root_1() {
        // GIVEN: 2 root pages
        let mut page_manager = PageManager::new_anon(257, 0).unwrap();
        let page0 = page_manager.allocate(42).unwrap();
        assert_eq!(page0.id(), 0);
        let mut root_page = RootPageMut::try_from(page0).unwrap();

        let page1 = page_manager.allocate(42).unwrap();
        assert_eq!(page1.id(), 1);

        // page 0 and 1 (root pages) allocated. allocate 254 more pages to simulate the
        // reserved pages
        for _ in 2..256 {
            page_manager.allocate(42).unwrap();
        }

        // WHEN: Root page 0 is filled with more orphan page ids than it can hold
        //
        // The root page can hold MAX_ORPHANS orphan page ids
        let expected_orphan_page_ids: Vec<PageId> = (1..2000).collect();
        root_page.set_orphaned_page_ids(&expected_orphan_page_ids, &mut page_manager).unwrap();

        // THEN: Page 1 should not be changed at all
        assert_eq!(page1.contents(), [0; Page::DATA_SIZE]);
    }

    #[test]
    fn test_orphan_list_writes_reserved_pages() {
        // GIVEN: 2 root pages with PageId 0 and PageId 1
        let mut page_manager = PageManager::new_anon(20, 0).unwrap();
        let mut root_page = page_manager.allocate(42).and_then(RootPageMut::try_from).unwrap();
        assert_eq!(root_page.id(), 0);

        let page1 = page_manager.allocate(42).unwrap();
        assert_eq!(page1.id(), 1);

        let first_reserved_page_for_orphan_ids =
            page_manager.allocate(42).and_then(OrphanListPageMut::try_from).unwrap();
        assert_eq!(first_reserved_page_for_orphan_ids.id(), 2);

        // WHEN: The remainder of the root page is maxed out with orphan page ids
        let orphan_page_ids = (1..MAX_ORPHANS as PageId + 1).collect::<Vec<PageId>>();
        root_page.set_orphaned_page_ids(&orphan_page_ids, &mut page_manager).unwrap();

        // THEN: Adding more orphan page ids should spill over to page 2
        let my_orphan_page_ids_for_page_2 = [1012, 1013, 1014, 1015];
        let total_new_page_ids = orphan_page_ids.iter().chain(&my_orphan_page_ids_for_page_2);
        root_page.set_orphaned_page_ids(total_new_page_ids, &mut page_manager).unwrap();

        assert_eq!(
            &root_page.data.orphaned_page_ids[..],
            orphan_page_ids.iter().copied().map(NonZero::new).collect::<Vec<_>>()
        );
        assert_eq!(
            &first_reserved_page_for_orphan_ids.data.orphaned_page_ids[..4],
            my_orphan_page_ids_for_page_2.iter().copied().map(NonZero::new).collect::<Vec<_>>()
        );
        assert_eq!(
            &first_reserved_page_for_orphan_ids.data.orphaned_page_ids[4..],
            std::iter::repeat_n(None, 1017).collect::<Vec<_>>()
        );

        assert_eq!(root_page.data.next, NonZero::new(first_reserved_page_for_orphan_ids.id()));
        assert_eq!(first_reserved_page_for_orphan_ids.data.next, None);

        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();
        assert_eq!(orphan_page_ids, (1..=1015).collect::<Vec<_>>());
    }

    #[test]
    fn test_orphan_list_allocates_after_reserved_pages() {
        // GIVEN: 256 pages with PageIds [0-255]
        let mut page_manager = PageManager::new_anon(257, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        assert_eq!(page.id(), 0);
        let mut root_page = RootPageMut::try_from(page).unwrap();

        // page 0 allocated. allocate 255 more pages
        for _ in 1..256 {
            page_manager.allocate(42).unwrap();
        }

        // WHEN: Pages 2-255 are filled with orphan ids
        //
        // The root page can hold MAX_ORPHANS orphan page ids and all the reserved pages
        // can hold 1021 (remember the last 4 bytes are reserved for the next page id
        // and the first 8 bytes are the header).
        // So total orphan pages is MAX_ORPHANS + (1021 * 254) == 260345
        let expected_orphan_page_ids: Vec<PageId> = (1..260346).collect();
        root_page.set_orphaned_page_ids(&expected_orphan_page_ids, &mut page_manager).unwrap();

        // THEN: Adding more orphan page ids should spill over to page 256, which
        // should only be allocated when the new orphan page ids are added
        match page_manager.get(42, 256 as PageId) {
            Err(PageError::PageNotFound(page_id)) => assert_eq!(page_id, 256),
            _ => panic!("page 256 should not be allocated yet"),
        }

        let my_orphan_page_ids_for_page_256: &[PageId] = &[260346, 260347, 260348, 260349];
        let total_new_page_ids: Vec<PageId> = expected_orphan_page_ids
            .iter()
            .chain(my_orphan_page_ids_for_page_256.iter())
            .copied()
            .collect();
        root_page.set_orphaned_page_ids(&total_new_page_ids, &mut page_manager).unwrap();

        let page_256 = page_manager.get(42, 256 as PageId).unwrap();
        let page_256_contents = page_256.contents();
        for (i, expected_orphan_page_id) in my_orphan_page_ids_for_page_256.iter().enumerate() {
            let start = i * 4;
            let end = start + 4;
            let orphan_page_id =
                PageId::from_le_bytes(page_256_contents[start..end].try_into().unwrap());
            assert_eq!(orphan_page_id, *expected_orphan_page_id)
        }
    }

    #[test]
    fn test_orphan_list_shrinks_to_empty() {
        // GIVEN: 256 pages with PageIds [0-255]
        let mut page_manager = PageManager::new_anon(257, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        assert_eq!(page.id(), 0);
        let mut root_page = RootPageMut::try_from(page).unwrap();

        // page 0 allocated. allocate 255 more pages
        for _ in 1..256 {
            page_manager.allocate(42).unwrap();
        }

        // WHEN: Pages 2-255 are filled with orphan ids and all orphan ids are popped off and used
        // with no new orphan ids
        //
        // The root page can hold MAX_ORPHANS orphan page ids and all the reserved pages
        // can hold 1021 (remember the last 4 bytes are reserved for the next page id
        // and the first 8 bytes are the header).
        // So total orphan pages is MAX_ORPHANS + (1021 * 254) == 260345
        let expected_orphan_page_ids: Vec<PageId> = (1..260346).collect();
        root_page.set_orphaned_page_ids(&expected_orphan_page_ids, &mut page_manager).unwrap();

        root_page.set_orphaned_page_ids(&[], &mut page_manager).unwrap();

        // THEN: No orphan ids should be returned
        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();
        assert_eq!(orphan_page_ids.len(), 0)
    }

    #[test]
    fn test_vecdeque_rotate_orphan_page_ids() {
        // GIVEN: a root page with orphan ids
        let mut page_manager = PageManager::new_anon(20, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        let mut root_page = RootPageMut::try_from(page).unwrap();
        let my_orphan_page_ids: &[PageId] = &[2, 3, 4, 5, 6, 7, 8, 9, 10];
        root_page.set_orphaned_page_ids(my_orphan_page_ids, &mut page_manager).unwrap();

        // WHEN: more than half of the list is "given out"
        let orphan_page_ids_left = &[8, 9, 10];
        root_page.set_orphaned_page_ids(orphan_page_ids_left, &mut page_manager).unwrap();

        // THEN: vecdeque rotate_right should not panic given that the num_orphan_slots_used is
        // greater than the new list to add.
        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();
        assert_eq!(orphan_page_ids_left.to_vec(), orphan_page_ids);
    }
}
