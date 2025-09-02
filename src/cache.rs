use crate::{page::PageId, snapshot::SnapshotId};
use alloy_trie::Nibbles;
use parking_lot::Mutex;
use std::{
    cell::RefCell,
    collections::HashMap,
    num::NonZeroUsize,
    rc::{Rc, Weak as RcWeak},
    sync::Arc,
};

/// Represents the location of a cached entry. Typically would be wrapped with `Option` to
/// represent no entry or if there was an explicit tombstone.
#[derive(Debug, PartialEq)]
pub enum CachedLocation {
    DeletedEntry,
    GlobalPosition(PageId, u8),
}

/// An entry in the versioned LRU cache.
#[derive(Debug, Clone)]
struct Entry {
    snapshot_id: SnapshotId,
    key: Nibbles,
    value: Option<(PageId, u8)>,
    lru_prev: Option<RcWeak<RefCell<Entry>>>,
    lru_next: Option<Rc<RefCell<Entry>>>,
}

impl Entry {
    fn new(snapshot_id: SnapshotId, key: Nibbles, value: Option<(PageId, u8)>) -> Self {
        Self { snapshot_id, key, value, lru_prev: None, lru_next: None }
    }
}

/// Versioned LRU cache is a doubly-linked list of `Entry`s.
///
/// The list is sorted by snapshot_id, and the most recent version is at the head.
/// The list is used to track the most recent versions of each key.
/// The list is also used to evict the least recent versions of each key when the cache is full.
#[derive(Debug)]
struct VersionedLru {
    // Sorted by snapshot_id
    entries: HashMap<Nibbles, Vec<Entry>>,

    // Keep track of the head and tail
    head: Option<Rc<RefCell<Entry>>>,
    tail: Option<RcWeak<RefCell<Entry>>>,
    capacity: usize,
    size: usize,

    // Proactively purge obsolete entries and free up cache space
    min_snapshot_id: SnapshotId,

    // Track highest snapshot_id that was ever evicted to maintain temporal coherence
    max_evicted_version: SnapshotId,
}

impl VersionedLru {
    fn new(capacity: usize) -> Self {
        Self {
            entries: HashMap::new(),
            head: None,
            tail: None,
            capacity,
            size: 0,
            min_snapshot_id: 0,
            max_evicted_version: 0,
        }
    }

    /// Finds the entry matching the key via `entries` with the largest snapshot_id <=
    /// target_snapshot_id. If the entry is found, it is moved to the front of the LRU list.
    fn get(&mut self, key: &Nibbles, target_snapshot_id: SnapshotId) -> Option<CachedLocation> {
        self.purge_outdated_entries(key);

        // Get entry, if no entry is found, return None
        let versions = self.entries.get(key)?;
        let entry_idx =
            versions.iter().rposition(|entry| entry.snapshot_id <= target_snapshot_id)?;
        let entry = &versions[entry_idx];

        // Find the entry in LRU list and move to front
        if let Some(value) = entry.value {
            self.move_to_front(key, entry.snapshot_id);
            Some(CachedLocation::GlobalPosition(value.0, value.1))
        } else {
            Some(CachedLocation::DeletedEntry)
        }
    }

    /// Creates a new entry, puts it at the front of the linked list, and inserts into `entries`.
    /// If the cache is full, evicts the tail entry and removes it from `entries`, and pops it from
    /// the linked list.
    fn set(&mut self, key: Nibbles, snapshot_id: SnapshotId, value: Option<(PageId, u8)>) {
        // Prevent insertion of entries older than max_evicted_version to maintain temporal
        // coherence
        if snapshot_id < self.max_evicted_version {
            return;
        }

        // Make entry and find appropriate position
        let versions = self.entries.entry(key.clone()).or_default();
        let entry = Entry::new(snapshot_id, key.clone(), value);
        let pos = versions
            .binary_search_by_key(&snapshot_id, |e| e.snapshot_id)
            .unwrap_or_else(|pos| pos);

        if pos < versions.len() && versions[pos].snapshot_id == snapshot_id {
            // existing entry, update it and move to front
            versions[pos] = entry;
            self.move_to_front(&key, snapshot_id);
        } else {
            // new entry
            versions.insert(pos, entry.clone());
            self.add_to_front(Rc::new(RefCell::new(entry.clone())));
            self.size += 1;
        }
        self.purge_outdated_entries(&key);

        // Cache full - remove leftmost entry
        if self.size > self.capacity {
            let Some(tail_entry) = self.tail.as_ref().and_then(|weak| weak.upgrade()) else {
                return
            };
            let tail_key = tail_entry.borrow().key.clone();

            let Some(leftmost_entry) =
                self.entries.get(&tail_key).and_then(|versions| versions.first())
            else {
                return
            };
            let leftmost_snapshot = leftmost_entry.snapshot_id;

            // Track max evicted version for temporal coherence
            self.max_evicted_version = self.max_evicted_version.max(leftmost_snapshot);

            // Find and remove the leftmost entry
            let Some(entry) = self.get_entry(&tail_key, leftmost_snapshot) else { return };
            self.remove(entry);
            self.size -= 1;

            // Remove leftmost entry from versions list
            if let Some(versions) = self.entries.get_mut(&tail_key) {
                versions.remove(0);
                if versions.is_empty() {
                    self.entries.remove(&tail_key);
                }
            }
        }
    }

    //////////////////////////////
    //// Helpers
    //////////////////////////////
    fn get_entry(&self, key: &Nibbles, snapshot_id: SnapshotId) -> Option<Rc<RefCell<Entry>>> {
        let mut current = self.head.clone();
        while let Some(entry) = current {
            if &entry.borrow().key == key && entry.borrow().snapshot_id == snapshot_id {
                return Some(entry);
            }
            current = entry.borrow().lru_next.clone();
        }
        None
    }

    /// Update head pointer and `Entry`'s pointers
    fn add_to_front(&mut self, entry: Rc<RefCell<Entry>>) {
        entry.borrow_mut().lru_prev = None;
        entry.borrow_mut().lru_next = self.head.clone();

        if let Some(old_head) = &self.head {
            old_head.borrow_mut().lru_prev = Some(Rc::downgrade(&entry));
        } else {
            self.tail = Some(Rc::downgrade(&entry));
        }

        self.head = Some(entry);
    }

    /// Remove an entry from LRU
    fn remove(&mut self, entry: Rc<RefCell<Entry>>) {
        let prev = entry.borrow().lru_prev.clone();
        let next = entry.borrow().lru_next.clone();

        if let Some(prev_entry) = prev.as_ref().and_then(|weak| weak.upgrade()) {
            prev_entry.borrow_mut().lru_next = next.clone();
        } else {
            self.head = next.clone();
        }

        if let Some(next_entry) = &next {
            next_entry.borrow_mut().lru_prev = prev.clone();
        } else {
            self.tail = prev;
        }

        entry.borrow_mut().lru_prev = None;
        entry.borrow_mut().lru_next = None;
    }

    /// Purging is done lazily in `get` and `set` methods
    fn set_min_snapshot_id(&mut self, min_snapshot_id: SnapshotId) {
        self.min_snapshot_id = min_snapshot_id;
    }

    /// Purges outdated entries while keeping at least one version with snapshot_id <= min_id
    /// to ensure queries at min_id still work.
    fn purge_outdated_entries(&mut self, key: &Nibbles) {
        if self.min_snapshot_id == 0 {
            return;
        }

        let Some(versions) = self.entries.get(key) else {
            return;
        };

        // Find the last entry with snapshot_id <= min_snapshot_id
        let Some(idx) =
            versions.iter().rposition(|entry| entry.snapshot_id <= self.min_snapshot_id)
        else {
            // No entries with snapshot_id <= min_snapshot_id, don't remove any
            return;
        };

        // Collect up to the last snapshot_id <= min_snapshot_id
        let remove_snapshots: Vec<SnapshotId> =
            versions.iter().take(idx).map(|entry| entry.snapshot_id).collect();

        // Remove entries from LRU and adjust size
        for snapshot_id in remove_snapshots {
            if let Some(entry) = self.get_entry(key, snapshot_id) {
                self.remove(entry);
                self.size -= 1;
            }
        }

        // Remove outdated entries from versions
        if let Some(versions) = self.entries.get_mut(key) {
            for _ in 0..idx {
                versions.remove(0);
            }
            if versions.is_empty() {
                self.entries.remove(key);
            }
        }
    }

    /// Updates the position of an entry in the LRU
    fn move_to_front(&mut self, key: &Nibbles, snapshot_id: SnapshotId) {
        if let Some(lru_entry) = self.get_entry(key, snapshot_id) {
            if let Some(head) = &self.head {
                if Rc::ptr_eq(head, &lru_entry) {
                    return;
                }
            }
            self.remove(lru_entry.clone());
            self.add_to_front(lru_entry);
        }
    }
}

// VersionedLru is only accessed through the Mutex
unsafe impl Send for Entry {}
unsafe impl Send for VersionedLru {}

/// Holds the shared versioned LRU cache.
#[derive(Debug, Clone)]
pub struct CacheManager {
    cache: Arc<Mutex<VersionedLru>>,
}

impl CacheManager {
    pub fn new(max_size: NonZeroUsize) -> Self {
        CacheManager { cache: Arc::new(Mutex::new(VersionedLru::new(max_size.get()))) }
    }

    /// Gets a value for the given key and snapshot ID and updates LRU state.
    pub fn get(&self, snapshot_id: SnapshotId, key: &Nibbles) -> Option<CachedLocation> {
        // Acquire lock since we move the `Entry` to the front of the LRU list each time
        // This is helpful because we'll want to cache an account on read to accelerate
        // reading its contract state.
        self.cache.lock().get(key, snapshot_id)
    }

    /// Inserts or updates an entry in the cache.
    pub fn insert(&self, snapshot_id: SnapshotId, key: Nibbles, value: Option<(PageId, u8)>) {
        self.cache.lock().set(key, snapshot_id, value);
    }

    /// Removes an entry from the cache by inserting a None value.
    pub fn remove(&self, snapshot_id: SnapshotId, key: Nibbles) {
        self.cache.lock().set(key, snapshot_id, None);
    }

    /// Sets the minimum snapshot ID for proactive cache purging.
    pub fn set_min_snapshot_id(&self, min_snapshot_id: SnapshotId) {
        self.cache.lock().set_min_snapshot_id(min_snapshot_id);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{thread, time::Duration};

    #[test]
    fn test_cache_reading_and_writing() {
        let cache = CacheManager::new(NonZeroUsize::new(10).unwrap());

        // first writer
        cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11)));
        cache.insert(200, Nibbles::from_nibbles([1]), Some((PageId::new(20).unwrap(), 21)));
        cache.insert(100, Nibbles::from_nibbles([2]), Some((PageId::new(12).unwrap(), 13)));

        // have some concurrent readers
        let cache_reader1 = cache.clone();
        let reader1 = thread::spawn(move || {
            let val1 = cache_reader1.get(100, &Nibbles::from_nibbles([1]));
            let val2 = cache_reader1.get(200, &Nibbles::from_nibbles([1]));
            assert_eq!(val1, Some(CachedLocation::GlobalPosition(PageId::new(10).unwrap(), 11)));
            assert_eq!(val2, Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21)));
            thread::sleep(Duration::from_millis(50));
        });

        let cache_reader2 = cache.clone();
        let reader2 = thread::spawn(move || {
            let val = cache_reader2.get(100, &Nibbles::from_nibbles([2]));
            assert_eq!(val, Some(CachedLocation::GlobalPosition(PageId::new(12).unwrap(), 13)));
            thread::sleep(Duration::from_millis(100));
        });

        // writer2
        let cache_writer2 = cache.clone();
        let writer2 = thread::spawn(move || {
            cache_writer2.insert(
                101,
                Nibbles::from_nibbles([3]),
                Some((PageId::new(14).unwrap(), 15)),
            );
            cache_writer2.insert(
                300,
                Nibbles::from_nibbles([1]),
                Some((PageId::new(30).unwrap(), 31)),
            );
        });

        reader1.join().unwrap();
        reader2.join().unwrap();
        writer2.join().unwrap();

        assert_eq!(
            cache.get(100, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(10).unwrap(), 11))
        );
        assert_eq!(
            cache.get(100, &Nibbles::from_nibbles([2])),
            Some(CachedLocation::GlobalPosition(PageId::new(12).unwrap(), 13))
        );
        assert_eq!(
            cache.get(101, &Nibbles::from_nibbles([3])),
            Some(CachedLocation::GlobalPosition(PageId::new(14).unwrap(), 15))
        );
        assert_eq!(
            cache.get(200, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21))
        );
        assert_eq!(
            cache.get(300, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(30).unwrap(), 31))
        );
        assert_eq!(cache.get(300, &Nibbles::from_nibbles([4])), None);
    }

    #[test]
    fn test_getting_different_snapshots() {
        let cache = CacheManager::new(NonZeroUsize::new(10).unwrap());

        cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11)));
        cache.insert(300, Nibbles::from_nibbles([1]), Some((PageId::new(30).unwrap(), 31)));
        cache.insert(200, Nibbles::from_nibbles([1]), Some((PageId::new(20).unwrap(), 21)));

        // exact same snapshots
        assert_eq!(
            cache.get(100, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(10).unwrap(), 11))
        );
        assert_eq!(
            cache.get(200, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21))
        );
        assert_eq!(
            cache.get(300, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(30).unwrap(), 31))
        );

        // different snapshots, but it should find the latest version <= target snapshot
        assert_eq!(
            cache.get(150, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(10).unwrap(), 11))
        );
        assert_eq!(
            cache.get(250, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21))
        );

        // snapshot too small, since snapshot < earliest
        assert_eq!(cache.get(50, &Nibbles::from_nibbles([1])), None);
    }

    #[test]
    fn test_invalidating_entries() {
        let cache = CacheManager::new(NonZeroUsize::new(10).unwrap());

        // insert a value
        cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11)));

        // invalidate it
        cache.insert(100, Nibbles::from_nibbles([1]), None);

        // try reading it - should return DeletedEntry (tombstone) not None
        assert_eq!(cache.get(100, &Nibbles::from_nibbles([1])), Some(CachedLocation::DeletedEntry));
    }

    #[test]
    fn test_min_snapshot_purging() {
        let cache = CacheManager::new(NonZeroUsize::new(10).unwrap());

        // insert entries with different snapshots
        cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11)));
        cache.insert(300, Nibbles::from_nibbles([1]), Some((PageId::new(30).unwrap(), 31)));
        cache.insert(200, Nibbles::from_nibbles([1]), Some((PageId::new(20).unwrap(), 21)));

        // set minimum snapshot ID to 250
        cache.set_min_snapshot_id(250);

        // purged entries before the last valid entry (snapshot 100 should be gone)
        assert_eq!(cache.get(100, &Nibbles::from_nibbles([1])), None);

        // keep the last entry with snapshot_id <= min_snapshot_id (200) for queries at
        // min_snapshot_id
        assert_eq!(
            cache.get(200, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21))
        );

        // keep entries above min snapshot
        assert_eq!(
            cache.get(300, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(30).unwrap(), 31))
        );

        // should be able to query at min_snapshot_id and get snapshot 200's value
        assert_eq!(
            cache.get(250, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21))
        );
    }

    #[test]
    fn test_oldest_sibling_eviction() {
        let cache = CacheManager::new(NonZeroUsize::new(4).unwrap());

        // multiple versions of key [1] out of order to ensure the oldest version is still evicted
        cache.insert(200, Nibbles::from_nibbles([1]), Some((PageId::new(20).unwrap(), 21)));
        cache.insert(300, Nibbles::from_nibbles([1]), Some((PageId::new(30).unwrap(), 31)));
        cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11))); // multiple versions of key [1] out of order to ensure the oldest version is still evicted

        // one entry for key [2]
        cache.insert(150, Nibbles::from_nibbles([2]), Some((PageId::new(15).unwrap(), 16)));

        // since the cache is full, should evict oldest sibling of tail entry
        cache.insert(400, Nibbles::from_nibbles([3]), Some((PageId::new(40).unwrap(), 41)));

        // snapshot 100 should be evicted
        assert_eq!(cache.get(100, &Nibbles::from_nibbles([1])), None);

        // rest should exist
        assert_eq!(
            cache.get(200, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21))
        );
        assert_eq!(
            cache.get(300, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(30).unwrap(), 31))
        );
        assert_eq!(
            cache.get(150, &Nibbles::from_nibbles([2])),
            Some(CachedLocation::GlobalPosition(PageId::new(15).unwrap(), 16))
        );
        assert_eq!(
            cache.get(400, &Nibbles::from_nibbles([3])),
            Some(CachedLocation::GlobalPosition(PageId::new(40).unwrap(), 41))
        );
    }

    #[test]
    fn test_temporal_coherence() {
        let cache = CacheManager::new(NonZeroUsize::new(2).unwrap());

        // insert entries
        cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11)));
        cache.insert(200, Nibbles::from_nibbles([2]), Some((PageId::new(20).unwrap(), 21)));

        // this should evict snapshot 100, setting max_evicted_version to 100
        cache.insert(300, Nibbles::from_nibbles([3]), Some((PageId::new(30).unwrap(), 31)));

        // this should be rejected since it's older than max_evicted_version
        cache.insert(50, Nibbles::from_nibbles([4]), Some((PageId::new(5).unwrap(), 6)));

        // should not be retrievable
        assert_eq!(cache.get(50, &Nibbles::from_nibbles([4])), None);

        // rest should still work
        assert_eq!(
            cache.get(200, &Nibbles::from_nibbles([2])),
            Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21))
        );
        assert_eq!(
            cache.get(300, &Nibbles::from_nibbles([3])),
            Some(CachedLocation::GlobalPosition(PageId::new(30).unwrap(), 31))
        );
    }
}
