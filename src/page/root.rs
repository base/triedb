use crate::{page::Page, snapshot::SnapshotId};
use alloy_primitives::B256;
use std::collections::VecDeque;
use std::iter::Peekable;

use super::{
    page::{PageKind, RO, RW},
    PageError, PageId, PageManager,
};

const MAX_ORPHANS: usize = 1011;

pub struct RootPage<'p, P: PageKind> {
    page: Page<'p, P>,
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

        Self { page: page_mut }
    }

    pub fn add_orphaned_page_ids<'a, T: PageManager>(
        &mut self,
        orphan_page_ids: &Vec<PageId>,
        num_orphan_slots_used: usize,
        page_manager: &mut T,
    ) -> Result<(), PageError> {
        // A "slot" can be thought of as a single orphan page_id which is 4 bytes.
        // We start at slot 10 (byte index 40 == 10*4) because the root page contains metadata before the orphan
        // list starts: state_root(32 bytes) + root_subtrie_page_number(4 bytes) + max_page_number(4 bytes)
        let current_slot_index = 10;
        let page = &mut self.page;

        // TODO: this can be optimized by storing the length of the on disk
        // list when opening the database.
        let original_list_on_disk = self.get_orphaned_page_ids(page_manager)?;
        if num_orphan_slots_used >= original_list_on_disk.len() {
            // all of our original orphan page ids on disk have been used.
            // we need to write the entire current in-memory list to disk.
            return RootPage::add_orphaned_page_ids_helper(
                self.snapshot_id(),
                &mut self.page,
                current_slot_index,
                orphan_page_ids.iter().peekable(),
                page_manager,
            );
        }

        // assuming a FIFO strategy from the orphan manager, the end of our list
        // should contain new elements if there are any. By rotating them to the
        // front of the list, we can minimize the number of elements we actually
        // have to write to disk.
        //
        // (e.g):
        // 1. on_disk: [1, 2, 3, 4, 5]
        // 2. 2 orphan pages are used: [3, 4, 5]
        // 3. 2 new orphan pages come in [3, 4, 5, 6, 7]
        // 4. Rotate right by 2: [7, 6, 3, 4, 5]
        // 5. When we write to disk only the first 2 slots change
        let mut deq: VecDeque<PageId> = VecDeque::from(orphan_page_ids.clone());
        deq.rotate_right(num_orphan_slots_used);
        RootPage::add_orphaned_page_ids_helper(
            self.snapshot_id(),
            &mut self.page,
            current_slot_index,
            deq.iter().peekable(),
            page_manager,
        )
    }

    fn add_orphaned_page_ids_helper<'a, T, I>(
        snapshot_id: SnapshotId,
        page: &mut Page<'p, RW>,
        mut current_slot_index: usize,
        mut orphan_page_ids: Peekable<I>,
        page_manager: &mut T,
    ) -> Result<(), PageError>
    where
        T: PageManager,
        I: Iterator<Item = &'a PageId>,
    {
        let current_page_id = page.page_id();
        let page_contents = page.contents_mut();
        let last_slot_index = (page_contents.len() / 4) - 1;
        if last_slot_index < 0 {
            // should be unreachable
            return Err(PageError::InvalidPageContents(current_page_id));
        }

        while let Some(_) = orphan_page_ids.peek() {
            let current_orphan_page_id_start_index = current_slot_index * 4;
            let current_orphan_page_id = u32::from_le_bytes(
                page_contents
                    [current_orphan_page_id_start_index..current_orphan_page_id_start_index + 4]
                    .try_into()
                    .expect("orphan page id is 4 bytes"),
            );

            if current_slot_index == last_slot_index {
                // the last slot is a special case that, if non-zero, indicates that the
                // orphan list continues at the page id stored in the last slot.

                let mut next_page: Page<'p, RW>;

                if current_orphan_page_id == 0 {
                    // we are at the end of the orphan list on disk but we have more elements
                    // to add. We need to create a new page or use a reserved page and
                    // write the new page's page id into the last slot of the current page.
                    if current_page_id >= 255 {
                        // Pages 2-255 are reserved for the orphan page list, but if we have
                        // more orphan page ids than the reserved section can hold, we need
                        // to allocate a new page and continue the list there
                        next_page = page_manager.allocate(snapshot_id)?;
                    } else {
                        // we must be in the "reserved" section (pages 2-255).
                        // move on to the next reserved page
                        let mut next_reserved_page = current_page_id + 1;
                        if next_reserved_page == 1 {
                            // special case where we are currently at root page 0,
                            // then the next page to continue the orphan page list
                            // is page id 2 (not 1)
                            next_reserved_page = next_reserved_page + 1
                        }
                        next_page = page_manager.get_mut(snapshot_id, next_reserved_page)?;
                    }

                    // Write the next_page page's id into the last slot of the current page,
                    // signaling that the list continues at the written page number.
                    page_contents[current_orphan_page_id_start_index
                        ..current_orphan_page_id_start_index + 4]
                        .copy_from_slice(&next_page.page_id().to_le_bytes());
                } else {
                    // the last slot is populated with a page id. we need to continue adding
                    // elements there
                    next_page = page_manager.get_mut(snapshot_id, current_orphan_page_id)?;
                }

                return RootPage::add_orphaned_page_ids_helper(
                    snapshot_id,
                    &mut next_page,
                    0,
                    orphan_page_ids,
                    page_manager,
                );
            }

            let orphan_page_id_to_write = orphan_page_ids.next().expect("value should be present");
            page_contents
                [current_orphan_page_id_start_index..current_orphan_page_id_start_index + 4]
                .copy_from_slice(&orphan_page_id_to_write.to_le_bytes());

            current_slot_index = current_slot_index + 1;
        }

        // We are done writing. Explicity set the next slot to 0 to
        // mark the end of the list.
        //
        // Note: it should be safe to always write the next slot at this point since our
        // last orphan page id write should always at least be before the last slot index.
        let current_orphan_page_id_start_index = current_slot_index * 4;
        page_contents[current_orphan_page_id_start_index..current_orphan_page_id_start_index + 4]
            .copy_from_slice(&0_u32.to_le_bytes());

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

        Ok(Self { page })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::page::MmapPageManager;
    use crate::page::PAGE_DATA_SIZE;
    use crate::page::PAGE_SIZE;

    #[test]
    fn test_add_get_orphan_page_ids() {
        // GIVEN: a root page with orphan ids
        let mut page_manager = MmapPageManager::new_anon(20, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        let mut root_page = RootPage::new(page, B256::default());
        let my_orphan_page_ids: &[PageId] = &[2, 3, 4, 5, 6, 7, 8, 9, 10];
        root_page
            .add_orphaned_page_ids(&my_orphan_page_ids.to_vec(), 0, &mut page_manager)
            .unwrap();

        // WHEN: the list of orphan ids are requested
        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();

        // THEN: the returned list of orphan page ids should match the original list
        assert_eq!(my_orphan_page_ids.to_vec(), orphan_page_ids);
    }

    #[test]
    fn test_get_empty_orphan_page_ids() {
        // GIVEN: a root page with no orphan ids
        let mut page_manager = MmapPageManager::new_anon(20, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        let mut root_page = RootPage::new(page, B256::default());

        // WHEN: the list of orphan ids are requested
        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();

        // THEN: the returned list of orphan page ids should be empty
        assert_eq!(orphan_page_ids.len(), 0);
    }

    #[test]
    fn test_2_page_orphan_page_ids() {
        // GIVEN: a root page with a list of orphan page ids spanning into page 2
        let mut page_manager = MmapPageManager::new_anon(20, 0).unwrap();
        let mut page0 = page_manager.allocate(42).unwrap();
        let mut page1 = page_manager.allocate(42).unwrap();
        let mut page2 = page_manager.allocate(42).unwrap();
        let mut my_orphan_page_ids: Vec<PageId> = Vec::new();

        let mut root_page = RootPage::new(page0, B256::default());
        // we should be able to store 1011 orphan page ids in a root page.
        // the last 4 bytes of the root page will be the next page id containing
        // the remainder of the list of orphan page ids
        let orphan_page_ids = (1..1012).map(|x| x as PageId).collect();
        root_page
            .add_orphaned_page_ids(&orphan_page_ids, 0, &mut page_manager)
            .unwrap();
        for i in orphan_page_ids.iter() {
            my_orphan_page_ids.push(*i);
        }

        // add the id of page2 to the last slot (4 bytes) of root page 1.
        // this will indicate that the orphan page list continues into page2
        let mut page0 = page_manager.get_mut(42, 0).unwrap();
        let data = page0.contents_mut();
        let size = data.len();
        data[size - 4..].copy_from_slice(&page2.page_id().to_le_bytes());

        // add more orphan page_ids to page 2
        let page2_data = page2.contents_mut();
        for i in 1011..2011 {
            let start = (i - 1011) * 4;
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
    fn test_add_replaces_used_slots() {
        // GIVEN: a root page with a list of orphan page ids
        let mut page_manager = MmapPageManager::new_anon(20, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        let mut root_page = RootPage::new(page, B256::default());
        let my_orphan_page_ids: &[PageId] = &[1, 2, 3, 4, 5, 6, 7, 8, 9];
        root_page
            .add_orphaned_page_ids(&my_orphan_page_ids.to_vec(), 0, &mut page_manager)
            .unwrap();

        // WHEN: The first 2 orphan page ids are used for new pages, and 2 new pages
        // are orphaned
        let num_orphan_slots_used = 2;
        root_page
            .add_orphaned_page_ids(
                &[3, 4, 5, 6, 7, 8, 9, 10, 11].to_vec(),
                num_orphan_slots_used,
                &mut page_manager,
            )
            .unwrap();

        // THEN: the first 2 "free" slots should be used to store the new orphan page ids
        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();
        let expected_orphan_page_ids: &[PageId] = &[10, 11, 3, 4, 5, 6, 7, 8, 9];
        assert_eq!(orphan_page_ids, expected_orphan_page_ids);
    }

    #[test]
    fn test_add_replaces_used_slots_across_pages() {
        // GIVEN: a root page with a list of orphan page ids spanning 2 pages
        let mut page_manager = MmapPageManager::new_anon(20, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        let mut root_page = RootPage::new(page, B256::default());

        // page 0 allocated. our pages for this test will spill into page 2
        // so allocate at least 2 more pages.
        for _ in 1..3 {
            page_manager.allocate(42).unwrap();
        }

        let mut my_orphan_page_ids: VecDeque<PageId> =
            VecDeque::from((1..2001).map(|x| x as PageId).collect::<Vec<PageId>>());
        root_page
            .add_orphaned_page_ids(
                &my_orphan_page_ids.iter().map(|x| *x).collect(),
                0,
                &mut page_manager,
            )
            .unwrap();

        // WHEN: The first 1050 orphan page ids are popped and 1050 new orphan page ids come in
        let num_orphan_slots_used = 1050;
        for i in 0..num_orphan_slots_used {
            my_orphan_page_ids.pop_front();
        }

        for i in 2000..3050 {
            my_orphan_page_ids.push_back(i);
        }

        root_page
            .add_orphaned_page_ids(
                &my_orphan_page_ids.iter().map(|x| *x).collect(),
                num_orphan_slots_used,
                &mut page_manager,
            )
            .unwrap();

        // THEN: the first 1050 "free" slots should be used to store the new orphan page ids
        let mut expected_orphan_page_ids: Vec<PageId> = (2000..3050).map(|x| x as PageId).collect();
        let mut remainder: Vec<PageId> = (1051..2001).map(|x| x as PageId).collect();
        expected_orphan_page_ids.append(&mut remainder);
        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();
        assert_eq!(orphan_page_ids, expected_orphan_page_ids);
    }

    #[test]
    fn test_add_replaces_used_slots_and_adds_to_end() {
        // GIVEN: a root page with a list of orphan page ids spanning 2 pages
        let mut page_manager = MmapPageManager::new_anon(20, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        let mut root_page = RootPage::new(page, B256::default());

        // page 0 allocated. our pages for this test will spill into page 2
        // so allocate at least 2 more pages.
        for _ in 1..4 {
            page_manager.allocate(42).unwrap();
        }

        let mut my_orphan_page_ids: VecDeque<PageId> =
            VecDeque::from((1..2001).map(|x| x as PageId).collect::<Vec<PageId>>());
        root_page
            .add_orphaned_page_ids(
                &my_orphan_page_ids.iter().map(|x| *x).collect(),
                0,
                &mut page_manager,
            )
            .unwrap();

        // WHEN: The first 20 orphan page ids are popped off and used for new pages, and 100 new pages
        // are orphaned
        let num_orphan_slots_used = 20;
        for i in 0..num_orphan_slots_used {
            my_orphan_page_ids.pop_front();
        }

        // adds 100 new orphan page ids
        for i in 2000..2100 {
            my_orphan_page_ids.push_back(i);
        }

        root_page
            .add_orphaned_page_ids(
                &my_orphan_page_ids.iter().map(|x| *x).collect(),
                num_orphan_slots_used,
                &mut page_manager,
            )
            .unwrap();

        // THEN: the first 20 "free" slots should be used to store the new orphan page ids and
        // the rest should be added to the end of the list
        //
        // the first 20 elements should match the last 20 elements of the new page ids id

        let mut expected_orphan_page_ids = my_orphan_page_ids.clone();
        expected_orphan_page_ids.rotate_right(num_orphan_slots_used);

        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();
        assert_eq!(
            orphan_page_ids,
            expected_orphan_page_ids
                .iter()
                .map(|x| *x)
                .collect::<Vec<PageId>>()
        );
    }

    #[test]
    fn test_root_0_doesnt_spill_into_root_1() {
        // GIVEN: 2 root pages
        let mut page_manager = MmapPageManager::new_anon(257, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        assert_eq!(page.page_id(), 0);
        let mut root_page = RootPage::new(page, B256::default());

        let page2 = page_manager.allocate(42).unwrap();
        assert_eq!(page2.page_id(), 1);

        // page 0 and 1 (root pages) allocated. allocate 254 more pages to simulate the
        // reserved pages
        for _ in 2..256 {
            page_manager.allocate(42).unwrap();
        }

        // WHEN: Root page 0 is filled with more orphan page ids than it can hold
        //
        // The root page can hold 1011 orphan page ids
        let expected_orphan_page_ids: Vec<PageId> = (1..2000).map(|x| x as PageId).collect();
        root_page
            .add_orphaned_page_ids(&expected_orphan_page_ids, 0, &mut page_manager)
            .unwrap();

        // THEN: Page 1 should not be changed at all
        assert_eq!(page2.contents(), [0; PAGE_DATA_SIZE]);
    }

    #[test]
    fn test_orphan_list_writes_reserved_pages() {
        // GIVEN: 2 root pages with PageId 0 and PageId 1
        let mut page_manager = MmapPageManager::new_anon(20, 0).unwrap();
        let page0 = page_manager.allocate(42).unwrap();
        assert_eq!(page0.page_id(), 0);
        let mut root_page = RootPage::new(page0, B256::default());

        let page1 = page_manager.allocate(42).unwrap();
        assert_eq!(page1.page_id(), 1);

        let first_reserved_page_for_orphan_ids = page_manager.allocate(42).unwrap();
        assert_eq!(first_reserved_page_for_orphan_ids.page_id(), 2);

        // WHEN: The remainder of the root page is maxed out with orphan page ids
        let orphan_page_ids = (1..1012).map(|x| x as PageId).collect();
        root_page
            .add_orphaned_page_ids(&orphan_page_ids, 0, &mut page_manager)
            .unwrap();

        // THEN: Adding more orphan page ids should spill over to page 2
        let my_orphan_page_ids_for_page_2: &[PageId] = &[1012, 1013, 1014, 1015];
        let total_new_page_ids: Vec<PageId> = orphan_page_ids
            .iter()
            .chain(my_orphan_page_ids_for_page_2.iter())
            .map(|x| *x)
            .collect();
        root_page
            .add_orphaned_page_ids(&total_new_page_ids, 0, &mut page_manager)
            .unwrap();

        let mut orphan_page_ids_page_2 = Vec::new();
        root_page
            .get_orphaned_page_ids_helper(
                first_reserved_page_for_orphan_ids.contents(),
                0,
                &mut orphan_page_ids_page_2,
                &page_manager,
            )
            .unwrap();

        assert_eq!(orphan_page_ids_page_2, my_orphan_page_ids_for_page_2);

        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();
        let expected_orphan_page_ids: Vec<PageId> = (1..1016).map(|x| x as PageId).collect();
        assert_eq!(orphan_page_ids, expected_orphan_page_ids);
    }

    #[test]
    fn test_orphan_list_allocates_after_reserved_pages() {
        // GIVEN: 256 pages with PageIds [0-255]
        let mut page_manager = MmapPageManager::new_anon(257, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        assert_eq!(page.page_id(), 0);
        let mut root_page = RootPage::new(page, B256::default());

        // page 0 allocated. allocate 255 more pages
        for _ in 1..256 {
            page_manager.allocate(42).unwrap();
        }

        // WHEN: Pages 2-255 are filled with orphan ids
        //
        // The root page can hold 1011 orphan page ids and all the reserved pages
        // can hold 1021 (remember the last 4 bytes are reserved for the next page id
        // and the first 8 bytes are the header).
        // So total orphan pages is 1011 + (1021 * 254) == 260345
        let expected_orphan_page_ids: Vec<PageId> = (1..260346).map(|x| x as PageId).collect();
        root_page
            .add_orphaned_page_ids(&expected_orphan_page_ids, 0, &mut page_manager)
            .unwrap();

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
            .map(|x| *x)
            .collect();
        root_page
            .add_orphaned_page_ids(&total_new_page_ids, 0, &mut page_manager)
            .unwrap();

        let page_256 = page_manager.get(42, 256 as PageId).unwrap();
        let page_256_contents = page_256.contents();
        for i in 0..my_orphan_page_ids_for_page_256.len() {
            let start = i * 4;
            let end = start + 4;
            let orphan_page_id =
                PageId::from_le_bytes(page_256_contents[start..end].try_into().unwrap());
            assert_eq!(orphan_page_id, my_orphan_page_ids_for_page_256[i])
        }
    }

    #[test]
    fn test_orphan_list_shrinks_to_empty() {
        // GIVEN: 256 pages with PageIds [0-255]
        let mut page_manager = MmapPageManager::new_anon(257, 0).unwrap();
        let page = page_manager.allocate(42).unwrap();
        assert_eq!(page.page_id(), 0);
        let mut root_page = RootPage::new(page, B256::default());

        // page 0 allocated. allocate 255 more pages
        for _ in 1..256 {
            page_manager.allocate(42).unwrap();
        }

        // WHEN: Pages 2-255 are filled with orphan ids and all orphan ids are popped off and used
        // with no new orphan ids
        //
        // The root page can hold 1011 orphan page ids and all the reserved pages
        // can hold 1021 (remember the last 4 bytes are reserved for the next page id
        // and the first 8 bytes are the header).
        // So total orphan pages is 1011 + (1021 * 254) == 260345
        let expected_orphan_page_ids: Vec<PageId> = (1..260346).map(|x| x as PageId).collect();
        root_page
            .add_orphaned_page_ids(&expected_orphan_page_ids, 0, &mut page_manager)
            .unwrap();

        let empty_new_orphan_ids = Vec::new();
        root_page
            .add_orphaned_page_ids(
                &empty_new_orphan_ids,
                expected_orphan_page_ids.len(),
                &mut page_manager,
            )
            .unwrap();

        // THEN: No orphan ids should be returned
        let orphan_page_ids = root_page.get_orphaned_page_ids(&page_manager).unwrap();
        assert_eq!(orphan_page_ids.len(), 0)
    }
}
