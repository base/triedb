use crate::{page::PageId, snapshot::SnapshotId};
use alloy_trie::Nibbles;
use std::{
    collections::HashMap,
    num::NonZeroUsize,
    sync::{Arc, Mutex, Weak},
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
    lru_prev: Option<Weak<Mutex<Entry>>>,
    lru_next: Option<Arc<Mutex<Entry>>>,
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
    head: Option<Arc<Mutex<Entry>>>,
    tail: Option<Weak<Mutex<Entry>>>,
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
            self.add_to_front(Arc::new(Mutex::new(entry.clone())));
            self.size += 1;
        }
        self.purge_outdated_entries(&key);

        // Cache full - evict oldest entry (tail)
        if self.size > self.capacity && self.tail.is_some() {
            if let Some(weak) = &self.tail {
                if let Some(tail_entry) = weak.upgrade() {
                    let tail_key = tail_entry.lock().unwrap().key.clone();

                    // Find oldest sibling (first entry in sorted versions list)
                    if let Some(versions) = self.entries.get(&tail_key) {
                        if let Some(oldest_sibling) = versions.first() {
                            let oldest_snapshot = oldest_sibling.snapshot_id;

                            // Track max evicted version for temporal coherence
                            self.max_evicted_version =
                                self.max_evicted_version.max(oldest_snapshot);

                            // Find and remove the oldest sibling from LRU
                            if let Some(lru_entry) = self.get_entry(&tail_key, oldest_snapshot) {
                                self.remove(lru_entry);
                                self.size -= 1;

                                if let Some(versions) = self.entries.get_mut(&tail_key) {
                                    // Remove leftmost entry
                                    versions.remove(0);
                                    if versions.is_empty() {
                                        self.entries.remove(&tail_key);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    //////////////////////////////
    //// Helpers
    //////////////////////////////
    fn get_entry(&self, key: &Nibbles, snapshot_id: SnapshotId) -> Option<Arc<Mutex<Entry>>> {
        let mut current = self.head.clone();
        while let Some(entry) = current {
            let guard = entry.lock().unwrap();
            if &guard.key == key && guard.snapshot_id == snapshot_id {
                drop(guard);
                return Some(entry);
            }
            current = guard.lru_next.clone();
        }
        None
    }

    /// Update head pointer and `Entry`'s pointers
    fn add_to_front(&mut self, entry: Arc<Mutex<Entry>>) {
        let mut guard = entry.lock().unwrap();
        guard.lru_prev = None;
        guard.lru_next = self.head.clone();
        drop(guard);

        if let Some(old_head) = &self.head {
            old_head.lock().unwrap().lru_prev = Some(Arc::downgrade(&entry));
        } else {
            self.tail = Some(Arc::downgrade(&entry));
        }

        self.head = Some(entry);
    }

    /// Remove an entry from LRU
    fn remove(&mut self, entry: Arc<Mutex<Entry>>) {
        let (prev, next) = {
            let entry_guard = entry.lock().unwrap();
            (entry_guard.lru_prev.clone(), entry_guard.lru_next.clone())
        };

        if let Some(weak) = &prev {
            if let Some(prev_entry) = weak.upgrade() {
                prev_entry.lock().unwrap().lru_next = next.clone();
            }
        } else {
            self.head = next.clone();
        }

        if let Some(next_entry) = &next {
            next_entry.lock().unwrap().lru_prev = prev.clone();
        } else {
            self.tail = prev;
        }

        let mut guard = entry.lock().unwrap();
        guard.lru_prev = None;
        guard.lru_next = None;
    }

    /// Purging is done lazily in `get` and `set` methods
    fn set_min_snapshot_id(&mut self, min_snapshot_id: SnapshotId) {
        self.min_snapshot_id = min_snapshot_id;
    }

    /// Finds the first entry with snapshot id less than min_id and removes it from the list
    fn purge_outdated_entries(&mut self, key: &Nibbles) {
        if let Some(versions) = self.entries.get_mut(key) {
            if let Some(idx) = versions.iter().position(|e| e.snapshot_id >= self.min_snapshot_id) {
                versions.drain(0..idx);
            }
        }
    }

    /// Updates the position of an entry in the LRU
    fn move_to_front(&mut self, key: &Nibbles, snapshot_id: SnapshotId) {
        if let Some(lru_entry) = self.get_entry(key, snapshot_id) {
            if let Some(head) = &self.head {
                if Arc::ptr_eq(head, &lru_entry) {
                    return;
                }
            }
            self.remove(lru_entry.clone());
            self.add_to_front(lru_entry);
        }
    }
}

/// Holds the shared versioned LRU cache.
#[derive(Debug)]
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
        let mut guard = self.cache.lock().unwrap();
        guard.get(key, snapshot_id)
    }

    /// Inserts or updates an entry in the cache.
    pub fn insert(&self, snapshot_id: SnapshotId, key: Nibbles, value: Option<(PageId, u8)>) {
        let mut guard = self.cache.lock().unwrap();
        guard.set(key, snapshot_id, value);
    }

    /// Removes an entry from the cache by inserting a None value.
    pub fn remove(&self, snapshot_id: SnapshotId, key: Nibbles) {
        let mut guard = self.cache.lock().unwrap();
        guard.set(key, snapshot_id, None);
    }

    /// Sets the minimum snapshot ID for proactive cache purging.
    pub fn set_min_snapshot_id(&self, min_snapshot_id: SnapshotId) {
        let mut guard = self.cache.lock().unwrap();
        guard.set_min_snapshot_id(min_snapshot_id);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{thread, time::Duration};

    #[test]
    fn test_cache_reading_and_writing() {
        let cache = CacheManager::new(NonZeroUsize::new(10).unwrap());
        let shared_cache = Arc::new(cache);

        // first writer
        shared_cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11)));
        shared_cache.insert(100, Nibbles::from_nibbles([2]), Some((PageId::new(12).unwrap(), 13)));
        shared_cache.insert(200, Nibbles::from_nibbles([1]), Some((PageId::new(20).unwrap(), 21)));

        // have some concurrent readers
        let cache_reader1 = Arc::clone(&shared_cache);
        let reader1 = thread::spawn(move || {
            let val1 = cache_reader1.get(100, &Nibbles::from_nibbles([1]));
            let val2 = cache_reader1.get(200, &Nibbles::from_nibbles([1]));
            assert_eq!(val1, Some(CachedLocation::GlobalPosition(PageId::new(10).unwrap(), 11)));
            assert_eq!(val2, Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21)));
            thread::sleep(Duration::from_millis(50));
        });

        let cache_reader2 = Arc::clone(&shared_cache);
        let reader2 = thread::spawn(move || {
            let val = cache_reader2.get(100, &Nibbles::from_nibbles([2]));
            assert_eq!(val, Some(CachedLocation::GlobalPosition(PageId::new(12).unwrap(), 13)));
            thread::sleep(Duration::from_millis(100));
        });

        // writer2
        let cache_writer2 = Arc::clone(&shared_cache);
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
            shared_cache.get(100, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(10).unwrap(), 11))
        );
        assert_eq!(
            shared_cache.get(100, &Nibbles::from_nibbles([2])),
            Some(CachedLocation::GlobalPosition(PageId::new(12).unwrap(), 13))
        );
        assert_eq!(
            shared_cache.get(101, &Nibbles::from_nibbles([3])),
            Some(CachedLocation::GlobalPosition(PageId::new(14).unwrap(), 15))
        );
        assert_eq!(
            shared_cache.get(200, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21))
        );
        assert_eq!(
            shared_cache.get(300, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(30).unwrap(), 31))
        );
        assert_eq!(shared_cache.get(300, &Nibbles::from_nibbles([4])), None);
    }

    #[test]
    fn test_getting_different_snapshots() {
        let cache = CacheManager::new(NonZeroUsize::new(10).unwrap());
        let shared_cache = Arc::new(cache);

        shared_cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11)));
        shared_cache.insert(200, Nibbles::from_nibbles([1]), Some((PageId::new(20).unwrap(), 21)));
        shared_cache.insert(300, Nibbles::from_nibbles([1]), Some((PageId::new(30).unwrap(), 31)));

        // exact same snapshots
        assert_eq!(
            shared_cache.get(100, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(10).unwrap(), 11))
        );
        assert_eq!(
            shared_cache.get(200, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21))
        );
        assert_eq!(
            shared_cache.get(300, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(30).unwrap(), 31))
        );

        // different snapshots, but it should find the latest version <= target snapshot
        assert_eq!(
            shared_cache.get(150, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(10).unwrap(), 11))
        );
        assert_eq!(
            shared_cache.get(250, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21))
        );

        // snapshot too small, since snapshot < earliest
        assert_eq!(shared_cache.get(50, &Nibbles::from_nibbles([1])), None);
    }

    #[test]
    fn test_invalidating_entries() {
        let cache = CacheManager::new(NonZeroUsize::new(10).unwrap());
        let shared_cache = Arc::new(cache);

        // insert a value
        shared_cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11)));

        // invalidate it
        shared_cache.insert(100, Nibbles::from_nibbles([1]), None);

        // try reading it - should return DeletedEntry (tombstone) not None
        assert_eq!(
            shared_cache.get(100, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::DeletedEntry)
        );
    }

    #[test]
    fn test_min_snapshot_purging() {
        let cache = CacheManager::new(NonZeroUsize::new(10).unwrap());
        let shared_cache = Arc::new(cache);

        // insert entries with different snapshots
        shared_cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11)));
        shared_cache.insert(200, Nibbles::from_nibbles([1]), Some((PageId::new(20).unwrap(), 21)));
        shared_cache.insert(300, Nibbles::from_nibbles([1]), Some((PageId::new(30).unwrap(), 31)));

        // set minimum snapshot ID to 250
        shared_cache.set_min_snapshot_id(250);

        // purged the entries below min snapshot
        assert_eq!(shared_cache.get(100, &Nibbles::from_nibbles([1])), None);
        assert_eq!(shared_cache.get(200, &Nibbles::from_nibbles([1])), None);

        // only keep entries above min snapshot
        assert_eq!(
            shared_cache.get(300, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(30).unwrap(), 31))
        );
    }

    #[test]
    fn test_oldest_sibling_eviction() {
        let cache = CacheManager::new(NonZeroUsize::new(4).unwrap());
        let shared_cache = Arc::new(cache);

        // multiple versions of key [1] out of order to ensure the oldest version is still evicted
        shared_cache.insert(200, Nibbles::from_nibbles([1]), Some((PageId::new(20).unwrap(), 21)));
        shared_cache.insert(300, Nibbles::from_nibbles([1]), Some((PageId::new(30).unwrap(), 31)));
        shared_cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11))); // multiple versions of key [1] out of order to ensure the oldest version is still evicted

        // one entry for key [2]
        shared_cache.insert(150, Nibbles::from_nibbles([2]), Some((PageId::new(15).unwrap(), 16)));

        // since the cache is full, should evict oldest sibling of tail entry
        shared_cache.insert(400, Nibbles::from_nibbles([3]), Some((PageId::new(40).unwrap(), 41)));

        // snapshot 100 should be evicted
        assert_eq!(shared_cache.get(100, &Nibbles::from_nibbles([1])), None);

        // rest should exist
        assert_eq!(
            shared_cache.get(200, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21))
        );
        assert_eq!(
            shared_cache.get(300, &Nibbles::from_nibbles([1])),
            Some(CachedLocation::GlobalPosition(PageId::new(30).unwrap(), 31))
        );
        assert_eq!(
            shared_cache.get(150, &Nibbles::from_nibbles([2])),
            Some(CachedLocation::GlobalPosition(PageId::new(15).unwrap(), 16))
        );
        assert_eq!(
            shared_cache.get(400, &Nibbles::from_nibbles([3])),
            Some(CachedLocation::GlobalPosition(PageId::new(40).unwrap(), 41))
        );
    }

    #[test]
    fn test_temporal_coherence() {
        let cache = CacheManager::new(NonZeroUsize::new(2).unwrap());
        let shared_cache = Arc::new(cache);

        // insert entries
        shared_cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11)));
        shared_cache.insert(200, Nibbles::from_nibbles([2]), Some((PageId::new(20).unwrap(), 21)));

        // this should evict snapshot 100, setting max_evicted_version to 100
        shared_cache.insert(300, Nibbles::from_nibbles([3]), Some((PageId::new(30).unwrap(), 31)));

        // this should be rejected since it's older than max_evicted_version
        shared_cache.insert(50, Nibbles::from_nibbles([4]), Some((PageId::new(5).unwrap(), 6)));

        // should not be retrievable
        assert_eq!(shared_cache.get(50, &Nibbles::from_nibbles([4])), None);

        // rest should still work
        assert_eq!(
            shared_cache.get(200, &Nibbles::from_nibbles([2])),
            Some(CachedLocation::GlobalPosition(PageId::new(20).unwrap(), 21))
        );
        assert_eq!(
            shared_cache.get(300, &Nibbles::from_nibbles([3])),
            Some(CachedLocation::GlobalPosition(PageId::new(30).unwrap(), 31))
        );
    }
}
