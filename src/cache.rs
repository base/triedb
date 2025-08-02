use crate::{page::PageId, snapshot::SnapshotId};
use alloy_trie::Nibbles;
use std::{
    collections::HashMap,
    num::NonZeroUsize,
    sync::{Arc, RwLock},
};

/// An entry in the versioned LRU cache with doubly-linked list indices.
#[derive(Debug, Clone)]
struct Entry {
    snapshot_id: SnapshotId,
    key: Nibbles,
    value: Option<(PageId, u8)>,
    lru_prev: Option<usize>,
    lru_next: Option<usize>,
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

    // Doubly-linked list of entries
    lru: Vec<Entry>,
    head: Option<usize>,
    tail: Option<usize>,
    capacity: usize,

    // Proactively purge obsolete entries and free up cache space
    min_snapshot_id: Option<SnapshotId>,
}

impl VersionedLru {
    fn new(capacity: usize) -> Self {
        Self {
            entries: HashMap::new(),
            lru: Vec::new(),
            head: None,
            tail: None,
            capacity,
            min_snapshot_id: None,
        }
    }

    /// Finds the entry matching the key via `entries` with the largest snapshot_id <=
    /// target_snapshot_id. If the entry is found, it is moved to the front of the LRU list.
    fn get(&mut self, key: &Nibbles, target_snapshot_id: SnapshotId) -> Option<(PageId, u8)> {
        let versions = self.entries.get(key)?;

        let entry_idx =
            versions.iter().rposition(|entry| entry.snapshot_id <= target_snapshot_id)?;

        let entry = &versions[entry_idx];
        if let Some(value) = entry.value {
            // Find the entry and move to front
            let snapshot_id = entry.snapshot_id;
            if let Some(lru_idx) = self
                .lru
                .iter()
                .position(|entry| &entry.key == key && entry.snapshot_id == snapshot_id)
            {
                self.remove(lru_idx);
                self.add_to_front(lru_idx);
            }
            Some(value)
        } else {
            None
        }
    }

    /// Creates a new entry, puts it at the front of the linked list, and inserts into `entries`.
    /// If the cache is full, evicts the tail entry and removes it from `entries`, and pops it from
    /// the linked list.
    fn set(&mut self, key: Nibbles, snapshot_id: SnapshotId, value: Option<(PageId, u8)>) {
        let new_entry = Entry::new(snapshot_id, key.clone(), value);

        // Add to `entries`
        let versions = self.entries.entry(key.clone()).or_default();
        versions.push(new_entry.clone());
        versions.sort_by_key(|e| e.snapshot_id);

        // Add to linked list
        let lru_idx = self.lru.len();
        self.lru.push(new_entry);
        self.add_to_front(lru_idx);

        // Cache full - evict smallest snapshot_id entry
        if self.lru.len() > self.capacity && self.tail.is_some() {
            let tail_idx = self.tail.unwrap();
            let tail_key = self.lru[tail_idx].key.clone();

            // Find smallest snapshot_id for this key
            let smallest = if let Some(versions) = self.entries.get(&tail_key) {
                versions.iter().map(|e| e.snapshot_id).min()
            } else {
                None
            };

            // Find the LRU index of the smallest snapshot_id
            if let Some(smallest) = smallest {
                let smallest_idx = self
                    .lru
                    .iter()
                    .position(|entry| entry.key == tail_key && entry.snapshot_id == smallest);

                // Remove from `entries` hashmap
                if let Some(evict_idx) = smallest_idx {
                    if let Some(versions) = self.entries.get_mut(&tail_key) {
                        versions.retain(|e| e.snapshot_id != smallest);
                        if versions.is_empty() {
                            self.entries.remove(&tail_key);
                        }
                    }

                    self.remove(evict_idx);
                }
            }
        }
    }

    //////////////////////////////
    //// Helpers
    //////////////////////////////
    fn add_to_front(&mut self, lru_idx: usize) {
        self.lru[lru_idx].lru_prev = None;
        self.lru[lru_idx].lru_next = self.head;

        if let Some(old_head_idx) = self.head {
            self.lru[old_head_idx].lru_prev = Some(lru_idx);
        } else {
            self.tail = Some(lru_idx);
        }

        self.head = Some(lru_idx);
    }

    fn remove(&mut self, lru_idx: usize) {
        let prev_idx = self.lru[lru_idx].lru_prev;
        let next_idx = self.lru[lru_idx].lru_next;

        if let Some(prev) = prev_idx {
            self.lru[prev].lru_next = next_idx;
        } else {
            self.head = next_idx;
        }

        if let Some(next) = next_idx {
            self.lru[next].lru_prev = prev_idx;
        } else {
            self.tail = prev_idx;
        }

        // Mark as removed
        self.lru[lru_idx].lru_prev = None;
        self.lru[lru_idx].lru_next = None;
    }

    fn set_min_snapshot_id(&mut self, min_snapshot_id: SnapshotId) {
        self.min_snapshot_id = Some(min_snapshot_id);

        // Purge obsolete entries
        if let Some(min_id) = self.min_snapshot_id {
            let keys_to_update: Vec<Nibbles> = self.entries.keys().cloned().collect();

            for key in keys_to_update {
                if let Some(versions) = self.entries.get_mut(&key) {
                    versions.retain(|entry| entry.snapshot_id >= min_id);

                    if versions.is_empty() {
                        self.entries.remove(&key);
                    }
                }
            }

            // Remove from LRU list
            self.lru.retain(|entry| entry.snapshot_id >= min_id);

            // Rebuild LRU pointers after retention
            self.head = None;
            self.tail = None;

            for i in 0..self.lru.len() {
                self.lru[i].lru_prev = if i > 0 { Some(i - 1) } else { None };
                self.lru[i].lru_next = if i < self.lru.len() - 1 { Some(i + 1) } else { None };
            }

            if !self.lru.is_empty() {
                self.head = Some(0);
                self.tail = Some(self.lru.len() - 1);
            }
        }
    }
}

/// Holds the shared versioned LRU cache.
#[derive(Debug)]
pub struct CacheManager {
    cache: Arc<RwLock<VersionedLru>>,
}

impl CacheManager {
    pub fn new(max_size: NonZeroUsize) -> Self {
        CacheManager { cache: Arc::new(RwLock::new(VersionedLru::new(max_size.get()))) }
    }

    /// Gets a value for the given key and snapshot ID and updates LRU state.
    pub fn get(&self, snapshot_id: SnapshotId, key: &Nibbles) -> Option<(PageId, u8)> {
        // Acquire write lock since we move the `Entry` to the front of the LRU list each time
        // This is helpful because we'll want to cache an account on read to accelerate
        // reading its contract state.
        let mut guard = self.cache.write().unwrap();
        guard.get(key, snapshot_id)
    }

    /// Inserts or updates an entry in the cache.
    pub fn insert(&self, snapshot_id: SnapshotId, key: Nibbles, value: Option<(PageId, u8)>) {
        let mut guard = self.cache.write().unwrap();
        guard.set(key, snapshot_id, value);
    }

    /// Removes an entry from the cache by inserting a None value.
    pub fn remove(&self, snapshot_id: SnapshotId, key: Nibbles) {
        let mut guard = self.cache.write().unwrap();
        guard.set(key, snapshot_id, None);
    }

    /// Sets the minimum snapshot ID for proactive cache purging.
    pub fn set_min_snapshot_id(&self, min_snapshot_id: SnapshotId) {
        let mut guard = self.cache.write().unwrap();
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
            assert_eq!(val1, Some((PageId::new(10).unwrap(), 11)));
            assert_eq!(val2, Some((PageId::new(20).unwrap(), 21)));
            thread::sleep(Duration::from_millis(50));
        });

        let cache_reader2 = Arc::clone(&shared_cache);
        let reader2 = thread::spawn(move || {
            let val = cache_reader2.get(100, &Nibbles::from_nibbles([2]));
            assert_eq!(val, Some((PageId::new(12).unwrap(), 13)));
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
            Some((PageId::new(10).unwrap(), 11))
        );
        assert_eq!(
            shared_cache.get(100, &Nibbles::from_nibbles([2])),
            Some((PageId::new(12).unwrap(), 13))
        );
        assert_eq!(
            shared_cache.get(101, &Nibbles::from_nibbles([3])),
            Some((PageId::new(14).unwrap(), 15))
        );
        assert_eq!(
            shared_cache.get(200, &Nibbles::from_nibbles([1])),
            Some((PageId::new(20).unwrap(), 21))
        );
        assert_eq!(
            shared_cache.get(300, &Nibbles::from_nibbles([1])),
            Some((PageId::new(30).unwrap(), 31))
        );
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
            Some((PageId::new(10).unwrap(), 11))
        );
        assert_eq!(
            shared_cache.get(200, &Nibbles::from_nibbles([1])),
            Some((PageId::new(20).unwrap(), 21))
        );
        assert_eq!(
            shared_cache.get(300, &Nibbles::from_nibbles([1])),
            Some((PageId::new(30).unwrap(), 31))
        );

        // different snapshots, but it should find the latest version <= target snapshot
        assert_eq!(
            shared_cache.get(150, &Nibbles::from_nibbles([1])),
            Some((PageId::new(10).unwrap(), 11))
        );
        assert_eq!(
            shared_cache.get(250, &Nibbles::from_nibbles([1])),
            Some((PageId::new(20).unwrap(), 21))
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

        // try reading it
        assert_eq!(shared_cache.get(100, &Nibbles::from_nibbles([1])), None);
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
            Some((PageId::new(30).unwrap(), 31))
        );
    }

    #[test]
    fn test_oldest_sibling_eviction() {
        let cache = CacheManager::new(NonZeroUsize::new(4).unwrap());
        let shared_cache = Arc::new(cache);

        // multiple versions of key [1]
        shared_cache.insert(100, Nibbles::from_nibbles([1]), Some((PageId::new(10).unwrap(), 11)));
        shared_cache.insert(200, Nibbles::from_nibbles([1]), Some((PageId::new(20).unwrap(), 21)));
        shared_cache.insert(300, Nibbles::from_nibbles([1]), Some((PageId::new(30).unwrap(), 31)));

        // one entry for key [2]
        shared_cache.insert(150, Nibbles::from_nibbles([2]), Some((PageId::new(15).unwrap(), 16)));

        // since the cache is full, should evict oldest sibling of tail entry
        shared_cache.insert(400, Nibbles::from_nibbles([3]), Some((PageId::new(40).unwrap(), 41)));

        // snapshot 100 should be evicted
        assert_eq!(shared_cache.get(100, &Nibbles::from_nibbles([1])), None);

        // rest should exist
        assert_eq!(
            shared_cache.get(200, &Nibbles::from_nibbles([1])),
            Some((PageId::new(20).unwrap(), 21))
        );
        assert_eq!(
            shared_cache.get(300, &Nibbles::from_nibbles([1])),
            Some((PageId::new(30).unwrap(), 31))
        );
        assert_eq!(
            shared_cache.get(150, &Nibbles::from_nibbles([2])),
            Some((PageId::new(15).unwrap(), 16))
        );
        assert_eq!(
            shared_cache.get(400, &Nibbles::from_nibbles([3])),
            Some((PageId::new(40).unwrap(), 41))
        );
    }
}
