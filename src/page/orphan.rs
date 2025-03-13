use crate::{page::PageId, snapshot::SnapshotId};
use std::collections::BTreeMap;

// Manages a collection of orphaned page ids, grouped by the snapshot id which created them.
#[derive(Debug)]
pub struct OrphanPageManager {
    unlocked_page_ids: Vec<PageId>,
    locked_page_ids: BTreeMap<SnapshotId, Vec<PageId>>,
    num_orphan_pages_used: usize,
}

impl Default for OrphanPageManager {
    fn default() -> Self {
        Self::new()
    }
}

impl OrphanPageManager {
    // Creates a new OrphanPageManager.
    pub fn new() -> Self {
        Self {
            unlocked_page_ids: Vec::new(),
            locked_page_ids: BTreeMap::new(),
            num_orphan_pages_used: 0,
        }
    }

    // Creates a new OrphanPageManager with provided unlocked page ids.
    pub fn new_with_unlocked_page_ids(unlocked_page_ids: Vec<PageId>) -> Self {
        Self { unlocked_page_ids, locked_page_ids: BTreeMap::new(), num_orphan_pages_used: 0 }
    }

    // Returns an unlocked orphaned page id, if one exists.
    pub fn get_orphaned_page_id(&mut self) -> Option<PageId> {
        self.unlocked_page_ids.pop().inspect(|_| {
            self.num_orphan_pages_used += 1;
        })
    }

    // Unlocks all pages that were locked as of the given snapshot id.
    pub fn unlock(&mut self, max_snapshot_id: SnapshotId) {
        let mut to_remove = Vec::new();
        for (snapshot_id, pages) in self.locked_page_ids.iter_mut() {
            // This is currently necessary because the same page may be added multiple times when
            // the page is split. TODO: revisit this behavior when splitting is
            // performed in a more deterministic fashion.
            pages.sort_unstable();
            pages.dedup();
            if *snapshot_id <= max_snapshot_id {
                self.unlocked_page_ids.append(pages);
                to_remove.push(*snapshot_id);
            }
        }
        for snapshot_id in to_remove {
            self.locked_page_ids.remove(&snapshot_id);
        }
    }

    // Adds a single page id to the orphaned page ids for the given snapshot id.
    pub fn add_orphaned_page_id(&mut self, snapshot_id: SnapshotId, page_id: PageId) {
        self.add_orphaned_page_ids(snapshot_id, vec![page_id]);
    }

    // Adds a collection of page ids to the orphaned page ids for the given snapshot id.
    pub fn add_orphaned_page_ids(
        &mut self,
        snapshot_id: SnapshotId,
        pages: impl IntoIterator<Item = PageId>,
    ) {
        self.locked_page_ids.entry(snapshot_id).or_default().extend(pages);
    }

    // Returns the number of orphan pages were given out
    pub fn get_num_orphan_pages_used(&self) -> usize {
        self.num_orphan_pages_used
    }

    // Resets the number of orphan pages were given out
    pub fn reset_num_orphan_pages_used(&mut self) {
        self.num_orphan_pages_used = 0
    }

    // Returns a flat iterator over all the orphaned page ids, locked and unlocked.
    pub fn iter(&self) -> impl Iterator<Item = &PageId> {
        self.unlocked_page_ids
            .iter()
            .chain(self.locked_page_ids.values().flat_map(|pages| pages.iter()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_orphaned_page_id() {
        let mut manager = OrphanPageManager::new();
        manager.add_orphaned_page_id(42, 0);
        assert_eq!(manager.get_orphaned_page_id(), None);

        manager.unlock(42);
        assert_eq!(manager.get_orphaned_page_id(), Some(0));
        assert_eq!(manager.get_orphaned_page_id(), None);
    }

    #[test]
    fn test_add_orphaned_page_ids() {
        let mut manager = OrphanPageManager::new();
        manager.add_orphaned_page_ids(42, vec![0, 1, 2]);
        assert_eq!(manager.get_orphaned_page_id(), None);

        manager.unlock(42);
        assert_eq!(manager.get_orphaned_page_id(), Some(2));
        assert_eq!(manager.get_orphaned_page_id(), Some(1));
        assert_eq!(manager.get_orphaned_page_id(), Some(0));
        assert_eq!(manager.get_orphaned_page_id(), None);
    }

    #[test]
    fn test_get_orphaned_page_id_with_multiple_snapshots() {
        let mut manager = OrphanPageManager::new();
        manager.add_orphaned_page_id(42, 0);
        manager.add_orphaned_page_id(43, 1);
        manager.add_orphaned_page_id(44, 2);
        assert_eq!(manager.get_orphaned_page_id(), None);

        manager.unlock(42);
        assert_eq!(manager.get_orphaned_page_id(), Some(0));
        assert_eq!(manager.get_orphaned_page_id(), None);

        manager.unlock(43);
        assert_eq!(manager.get_orphaned_page_id(), Some(1));
        assert_eq!(manager.get_orphaned_page_id(), None);

        let mut manager = OrphanPageManager::new();
        manager.add_orphaned_page_id(42, 0);
        manager.add_orphaned_page_id(42, 1);
        manager.add_orphaned_page_id(43, 2);
        manager.add_orphaned_page_id(43, 3);
        manager.add_orphaned_page_id(44, 4);
        assert_eq!(manager.get_orphaned_page_id(), None);

        manager.unlock(43);
        assert_eq!(manager.get_orphaned_page_id(), Some(3));
        assert_eq!(manager.get_orphaned_page_id(), Some(2));
        assert_eq!(manager.get_orphaned_page_id(), Some(1));
        assert_eq!(manager.get_orphaned_page_id(), Some(0));
        assert_eq!(manager.get_orphaned_page_id(), None);
    }

    #[test]
    fn test_iter() {
        let mut manager = OrphanPageManager::new();
        manager.add_orphaned_page_ids(42, vec![0, 1, 2]);
        manager.add_orphaned_page_ids(999, vec![100, 101, 102]);
        let orphaned_page_ids: Vec<PageId> = manager.iter().copied().collect();
        assert_eq!(orphaned_page_ids, vec![0, 1, 2, 100, 101, 102]);
    }
}
