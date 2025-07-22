use crate::{page::PageId, snapshot::SnapshotId};
use alloy_trie::Nibbles;
use lru::LruCache;
use std::{
    collections::HashMap,
    num::NonZeroUsize,
    sync::{Arc, RwLock, RwLockReadGuard},
};

/// Type alias for contract_account_loc_cache
type ContractAccountLocCache = LruCache<Nibbles, (PageId, u8)>;
/// Type alias for mapping snapshot_id to contract_account_loc_cache
type Cache = HashMap<SnapshotId, ContractAccountLocCache>;

/// Holds the shared cache protected by an RwLock.
#[derive(Debug)]
pub struct CacheManager {
    /// The shared mapping of snapshots to cache.
    cache: Arc<RwLock<Cache>>,
    /// Maximum size of each contract_account_loc_cache.
    max_size: NonZeroUsize,
}

impl CacheManager {
    pub fn new(max_size: NonZeroUsize) -> Self {
        CacheManager { cache: Arc::new(RwLock::new(HashMap::new())), max_size }
    }

    /// Provides a reader handle to the cache.
    /// Multiple readers can exist concurrently.
    pub fn read(&self) -> Reader {
        Reader { guard: self.cache.read().unwrap() }
    }

    /// Provides a writer handle to the cache.
    /// This briefly acquires a lock to clone the cache, then releases it.
    pub fn write(&self) -> Writer {
        let cloned = {
            let guard = self.cache.read().unwrap();
            (*guard).clone()
        }; // Read lock is released here

        Writer { cache: Arc::clone(&self.cache), changes: cloned, max_size: self.max_size }
    }
}

/// A handle for reading from the cache.
/// Dropping this struct releases the read lock.
#[derive(Debug)]
pub struct Reader<'a> {
    guard: RwLockReadGuard<'a, Cache>,
}

impl<'a> Reader<'a> {
    /// Tries to get a value without updating LRU state from a specific inner LruCache.
    pub fn get(&self, outer_key: SnapshotId, inner_key: Nibbles) -> Option<&(PageId, u8)> {
        self.guard.get(&outer_key).and_then(|lru_cache| lru_cache.peek(&inner_key))
    }
}

/// A handle for writing to the cache.
/// Modifications are made to a clone, and committed back when `commit` is called.
/// Dropping this struct without calling `commit` will discard changes.
#[derive(Debug)]
pub struct Writer {
    cache: Arc<RwLock<Cache>>,
    changes: Cache, // The writer's own mutable copy of the cache
    max_size: NonZeroUsize,
}

impl Writer {
    /// Inserts or updates an entry in the cache.
    pub fn insert(&mut self, outer_key: SnapshotId, inner_key: Nibbles, value: (PageId, u8)) {
        self.changes
            .entry(outer_key)
            .or_insert_with(|| LruCache::new(self.max_size))
            .put(inner_key, value);
    }

    /// Removes an entry from the cache.
    pub fn remove(&mut self, outer_key: SnapshotId, inner_key: Nibbles) {
        self.changes.get_mut(&outer_key).and_then(|lru_cache| lru_cache.pop(&inner_key));
    }

    /// Commits the changes made by the writer back to the main shared cache.
    /// This consumes the `Writer`, acquiring a write lock only for the commit operation.
    pub fn commit(self) {
        let mut guard = self.cache.write().unwrap();
        *guard = self.changes;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{thread, time::Duration};

    #[test]
    fn test_concurrent_cache_read_write() {
        let cache = CacheManager::new(NonZeroUsize::new(2).unwrap());
        let shared_cache = Arc::new(cache); // Make it shareable across threads

        // --- Initial Write ---
        let mut writer1 = shared_cache.write();
        writer1.insert(100, Nibbles::from_nibbles([1]), (PageId::new(10).unwrap(), 11));
        writer1.insert(100, Nibbles::from_nibbles([2]), (PageId::new(12).unwrap(), 13));
        writer1.insert(200, Nibbles::from_nibbles([1]), (PageId::new(20).unwrap(), 21));

        // --- Concurrent Reads ---
        let cache_clone_for_reader1 = Arc::clone(&shared_cache);
        let reader_thread1 = thread::spawn(move || {
            let reader = cache_clone_for_reader1.read();
            let val1 = reader.get(100, Nibbles::from_nibbles([1]));
            let val2 = reader.get(200, Nibbles::from_nibbles([1]));
            assert_eq!(val1, Some(&(PageId::new(10).unwrap(), 11)));
            assert_eq!(val2, Some(&(PageId::new(20).unwrap(), 21)));
            // Simulate some work
            thread::sleep(Duration::from_millis(50));
            // Reader guard is dropped here automatically
        });

        // Start reading before Writer1 even commits, this should still work
        writer1.commit();

        let cache_clone_for_reader2 = Arc::clone(&shared_cache);
        let reader_thread2 = thread::spawn(move || {
            let reader = cache_clone_for_reader2.read();
            let val = reader.get(100, Nibbles::from_nibbles([2]));
            assert_eq!(val, Some(&(PageId::new(12).unwrap(), 13)));
            thread::sleep(Duration::from_millis(100));
        });

        // --- Writer attempting to write while readers are active ---
        // This writer will block until readers release their locks.
        let cache_clone_for_writer2 = Arc::clone(&shared_cache);
        let writer_thread2 = thread::spawn(move || {
            let mut writer = cache_clone_for_writer2.write(); // Blocks here
            writer.insert(100, Nibbles::from_nibbles([3]), (PageId::new(14).unwrap(), 15));
            writer.insert(300, Nibbles::from_nibbles([1]), (PageId::new(30).unwrap(), 31)); // New outer key
            writer.commit();
        });

        // Wait for all threads to complete
        reader_thread1.join().unwrap();
        reader_thread2.join().unwrap();
        writer_thread2.join().unwrap();

        // --- Verify Final State ---
        let final_reader = shared_cache.read();
        // writer2's changes was cloned after writer1 committed, so it contains writer1's data
        // plus writer2's additions However, the LRU cache for key 100 has capacity 2, so
        // adding a third entry evicts the oldest one
        assert_eq!(final_reader.get(100, Nibbles::from_nibbles([1])), None); // From writer1 that's evicted
        assert_eq!(
            final_reader.get(100, Nibbles::from_nibbles([3])),
            Some(&(PageId::new(14).unwrap(), 15))
        ); // Added by writer 2
        assert_eq!(
            final_reader.get(200, Nibbles::from_nibbles([1])),
            Some(&(PageId::new(20).unwrap(), 21))
        ); // From writer1
        assert_eq!(
            final_reader.get(300, Nibbles::from_nibbles([1])),
            Some(&(PageId::new(30).unwrap(), 31))
        ); // Added by writer 2
    }

    #[test]
    fn test_lru_behavior_within_writer() {
        let cache = CacheManager::new(NonZeroUsize::new(2).unwrap());
        let shared_cache = Arc::new(cache);

        // Insert some entries
        let mut writer = shared_cache.write();
        writer.insert(1, Nibbles::from_nibbles([1]), (PageId::new(1).unwrap(), 1));
        writer.insert(1, Nibbles::from_nibbles([2]), (PageId::new(2).unwrap(), 2));
        writer.insert(1, Nibbles::from_nibbles([3]), (PageId::new(3).unwrap(), 3)); // Should evict (1,1) if LRU working
        writer.commit();

        // Try reading the entries
        let reader = shared_cache.read();
        assert_eq!(reader.get(1, Nibbles::from_nibbles([1])), None); // (1,1) should be evicted
        assert_eq!(reader.get(1, Nibbles::from_nibbles([2])), Some(&(PageId::new(2).unwrap(), 2)));
        assert_eq!(reader.get(1, Nibbles::from_nibbles([3])), Some(&(PageId::new(3).unwrap(), 3)));
    }

    #[test]
    fn test_writer_remove() {
        let cache = CacheManager::new(NonZeroUsize::new(2).unwrap());
        let shared_cache = Arc::new(cache);

        // Insert some entries
        let mut writer1 = shared_cache.write();
        writer1.insert(100, Nibbles::from_nibbles([1]), (PageId::new(10).unwrap(), 11));
        writer1.insert(100, Nibbles::from_nibbles([2]), (PageId::new(12).unwrap(), 13));
        writer1.insert(200, Nibbles::from_nibbles([1]), (PageId::new(20).unwrap(), 21));
        writer1.commit();

        // Verify entries exist
        let reader = shared_cache.read();
        assert_eq!(
            reader.get(100, Nibbles::from_nibbles([1])),
            Some(&(PageId::new(10).unwrap(), 11))
        );
        assert_eq!(
            reader.get(100, Nibbles::from_nibbles([2])),
            Some(&(PageId::new(12).unwrap(), 13))
        );
        assert_eq!(
            reader.get(200, Nibbles::from_nibbles([1])),
            Some(&(PageId::new(20).unwrap(), 21))
        );
        drop(reader);

        // Remove an entry using Writer
        let mut writer2 = shared_cache.write();
        writer2.remove(100, Nibbles::from_nibbles([1]));
        writer2.commit();

        // Verify the entry is removed from shared state
        let final_reader = shared_cache.read();
        assert_eq!(final_reader.get(100, Nibbles::from_nibbles([1])), None); // Should be removed
        assert_eq!(
            final_reader.get(100, Nibbles::from_nibbles([2])),
            Some(&(PageId::new(12).unwrap(), 13))
        ); // Should still exist
        assert_eq!(
            final_reader.get(200, Nibbles::from_nibbles([1])),
            Some(&(PageId::new(20).unwrap(), 21))
        ); // Should still exist
    }
}
