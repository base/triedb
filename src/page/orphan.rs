use std::collections::BTreeMap;
use crate::snapshot::SnapshotId;
use crate::page::PageId;

// Manages a collection of orphaned page ids, grouped by the snapshot id which created them.
#[derive(Debug)]
pub struct OrphanPageManager {
    orphaned_page_ids: BTreeMap<SnapshotId, Vec<PageId>>,
}

impl OrphanPageManager {
    // Creates a new OrphanPageManager.
    pub fn new() -> Self {
        Self { orphaned_page_ids: BTreeMap::new() }
    }

    // Returns the page id of a page that was orphaned as of the given snapshot id.
    // If there are no orphaned pages as of the given snapshot id, None is returned.
    pub fn get_orphaned_page_id(&mut self, max_snapshot_id: SnapshotId) -> Option<PageId> {
        let (snapshot_id, pages) = self.orphaned_page_ids.iter_mut().find(|(k, _)| **k <= max_snapshot_id)?;
        let page_id = pages.pop();
        if pages.is_empty() {
            let to_remove = *snapshot_id;
            self.orphaned_page_ids.remove(&to_remove);
        }
        page_id
    }

    // Adds a single page id to the orphaned page ids for the given snapshot id.
    pub fn add_orphaned_page_id(&mut self, snapshot_id: SnapshotId, page_id: PageId) {
        self.add_orphaned_page_ids(snapshot_id, vec![page_id]);
    }

    // Adds a collection of page ids to the orphaned page ids for the given snapshot id.
    pub fn add_orphaned_page_ids(&mut self, snapshot_id: SnapshotId, pages: impl IntoIterator<Item = PageId>) {
        self.orphaned_page_ids.entry(snapshot_id).or_default().extend(pages);
    }

    // Returns an iterator over all the orphaned page ids.
    pub fn iter(&self) -> impl Iterator<Item = &PageId> {
        self.orphaned_page_ids.values().flat_map(|pages| pages.iter())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_orphaned_page_id() {
        let mut manager = OrphanPageManager::new();
        manager.add_orphaned_page_id(42, 0);
        assert_eq!(manager.get_orphaned_page_id(42), Some(0));
        assert_eq!(manager.get_orphaned_page_id(42), None);
    }

    #[test]
    fn test_add_orphaned_page_ids() {
        let mut manager = OrphanPageManager::new();
        manager.add_orphaned_page_ids(42, vec![0, 1, 2]);
        assert_eq!(manager.get_orphaned_page_id(42), Some(2));
        assert_eq!(manager.get_orphaned_page_id(42), Some(1));
        assert_eq!(manager.get_orphaned_page_id(42), Some(0));
        assert_eq!(manager.get_orphaned_page_id(42), None);
    }

    #[test]
    fn test_get_orphaned_page_id_with_multiple_snapshots() {
        let mut manager = OrphanPageManager::new();
        manager.add_orphaned_page_id(42, 0);
        manager.add_orphaned_page_id(43, 1);
        manager.add_orphaned_page_id(44, 2);
        assert_eq!(manager.get_orphaned_page_id(42), Some(0));
        assert_eq!(manager.get_orphaned_page_id(42), None);
        assert_eq!(manager.get_orphaned_page_id(43), Some(1));
        assert_eq!(manager.get_orphaned_page_id(43), None);

        let mut manager = OrphanPageManager::new();
        manager.add_orphaned_page_id(42, 0);
        manager.add_orphaned_page_id(43, 1);
        manager.add_orphaned_page_id(44, 2);
        assert_eq!(manager.get_orphaned_page_id(43), Some(0));
        assert_eq!(manager.get_orphaned_page_id(43), Some(1));
        assert_eq!(manager.get_orphaned_page_id(43), None);
        assert_eq!(manager.get_orphaned_page_id(42), None);
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
