use alloy_trie::Nibbles;
use lru::LruCache;
use std::{collections::HashMap, num::NonZeroUsize, sync::{Arc, RwLock}};

use crate::{page::PageId, snapshot::SnapshotId};

/// A cache manager that maintains the account-location cache centrally with a snapshot-based
/// architecture. Writers get a clone of the latest cache to work with, while readers get
/// shared references (RWLock) to the cache for their snapshot. This ensures that:
/// 1. Writers can always update the latest canonical cache version to match the current snapshot
/// 2. New readers can be created with a valid cache matching their snapshot
/// 3. Long-running readers don't block writers, but may force the DB to hold onto old pages
#[derive(Debug)]
pub struct CacheManager {
    /// Latest canonical cache that new transactions start from
    latest_cache: Arc<RwLock<LruCache<Nibbles, (PageId, u8)>>>,
    /// Map from snapshot ID to shared cache instances for readers
    reader_caches: HashMap<SnapshotId, Arc<RwLock<LruCache<Nibbles, (PageId, u8)>>>>,
}

impl CacheManager {
    pub fn new(max_cache_size: usize) -> Self {
        let latest_cache = Arc::new(RwLock::new(
            LruCache::new(NonZeroUsize::new(max_cache_size).unwrap())
        ));
        
        Self {
            latest_cache,
            reader_caches: HashMap::new(),
        }
    }

    /// Get a shared reference to the cache for a reader transaction
    /// Multiple readers at the same snapshot share the same cache instance
    pub fn get_reader_cache(&mut self, snapshot_id: SnapshotId) -> Arc<RwLock<LruCache<Nibbles, (PageId, u8)>>> {
        if let Some(cache) = self.reader_caches.get(&snapshot_id) {
            return Arc::clone(cache);
        }

        // Create a new cache for this snapshot by cloning the latest cache
        let new_cache = {
            let latest = self.latest_cache.read().unwrap();
            let cloned_cache = latest.clone();
            Arc::new(RwLock::new(cloned_cache))
        };

        self.reader_caches.insert(snapshot_id, Arc::clone(&new_cache));
        new_cache
    }

    /// Get a cloned cache for a writer transaction
    /// Writers get their own copy that they can modify freely
    pub fn get_writer_cache(&self) -> LruCache<Nibbles, (PageId, u8)> {
        let latest = self.latest_cache.read().unwrap();
        latest.clone()
    }

    /// Update the canonical cache version with the writer's modified cache
    /// This should be called when a writer transaction commits
    pub fn update_canonical_cache(&self, writer_cache: LruCache<Nibbles, (PageId, u8)>) {
        let mut latest = self.latest_cache.write().unwrap();
        *latest = writer_cache;
    }

    /// Clear a specific snapshot's cache and remove it entirely
    /// This should be called when a snapshot is no longer reserved
    pub fn clear_reader_cache(&mut self, snapshot_id: SnapshotId) {
        self.reader_caches.remove(&snapshot_id);
    }
}
