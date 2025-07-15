use alloy_trie::Nibbles;
use lru::LruCache;
use std::{collections::HashMap, num::NonZeroUsize, sync::{Arc, RwLock}};

use crate::{page::PageId, snapshot::SnapshotId};

/// A cache manager that maintains the account-location cache centrally instead of
/// per-transaction. Since the reader and writer transactions can be operating on different
/// versions of the trie simultaneously, the cache would need to be scoped to a single snapshot
/// version. Ideally when a writer transaction is committed, we should save its cache and use
/// this (or a copy of it) for new readers and writers.
///
/// Ideally this would contain a map of LRU caches, instead of an LRU cache of maps. We would map from snapshot id to cache.
/// Conceptually multiple readers at the same snapshot should be able to use the same cache instance and benefit each other if they access the same keys.
/// With only writer transactions, the writer would take the cache, update it (invalidating keys as needed), and then return it to the central repository on commit.
/// This cache management may need to be fairly coupled to the transaction manager (or management logic), as we would purge a cache instance once its snapshot is no longer reserved
#[derive(Debug)]
pub struct CacheManager {
    /// The maximum size per individual cache
    max_cache_size: usize,
    /// Map from snapshot ID to LRU cache - each snapshot gets its own cache instance
    caches: HashMap<SnapshotId, LruCache<Nibbles, (PageId, u8)>>,
}

impl CacheManager {
    pub fn new(max_cache_size: usize) -> Self {
        Self { 
            max_cache_size: max_cache_size,
            caches: HashMap::new(),
        }
    }

    /// Get/add a per-transaction cache for current snapshotID
    /// Multiple readers at the same snapshot share the same cache instance
    pub fn get_cache(&mut self, snapshot_id: SnapshotId) -> &mut LruCache<Nibbles, (PageId, u8)> {
        // If cache doesn't exist for this snapshot, create a new one
        if !self.caches.contains_key(&snapshot_id) {
            // Find the oldest snapshot (this is simple but not optimal - could use LRU for snapshots too)
            if let Some(&oldest_snapshot) = self.caches.keys().min() {
                self.caches.remove(&oldest_snapshot);
            }
            
            self.caches.insert(
                snapshot_id,
                LruCache::new(NonZeroUsize::new(self.max_cache_size).unwrap())
            );
        }

        self.caches.get_mut(&snapshot_id).unwrap()
    }

    /// Save a writer transaction's cache - in the new architecture, 
    /// the cache is already shared and updated in place
    pub fn save_cache(&mut self, snapshot_id: SnapshotId) {
        // With the new architecture, the cache is already shared and persisted
        // Writers update the cache in place, so no additional action needed
        // This method is kept for API compatibility
        let _ = snapshot_id; // Suppress unused variable warning
    }

    /// Clear a specific snapshot's cache and remove it entirely
    /// This should be called when a snapshot is no longer reserved
    pub fn clear_cache(&mut self, snapshot_id: SnapshotId) {
        self.caches.remove(&snapshot_id);
    }
}
