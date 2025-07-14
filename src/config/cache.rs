use lru::LruCache;
use std::num::NonZeroUsize;

use crate::{context::B512Map, page::PageId, snapshot::SnapshotId};

/// A cache manager that maintains the account-location cache centrally instead of
/// per-transaction. Since the reader and writer transactions can be operating on different
/// versions of the trie simultaneously, the cache would need to be scoped to a single snapshot
/// version. Ideally when a writer transaction is committed, we should save its cache and use
/// this (or a copy of it) for new readers and writers.
#[derive(Debug, Clone)]
pub struct CacheManager {
    /// The maximum size of [`caches`]. Once we start reusing the cache, it could grow infinitely,
    /// so we would need to cap its size as an LRU cache instead of a simple HashMap
    pub max_size: usize,
    /// Cache by snapshotID with LRU eviction
    caches: LruCache<SnapshotId, B512Map<(PageId, u8)>>,
}

impl CacheManager {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_max_size(&mut self, max_size: usize) -> &mut Self {
        self.max_size = max_size;
        self
    }

    /// Get/add a per-transaction cache for current snapshotID
    /// It uses the most recently used cache if available
    pub fn get_cache(&mut self, snapshot_id: SnapshotId) -> &mut B512Map<(PageId, u8)> {
        // The snapshot doesn't exist but we have a copy of the most recent cache
        // so use this for the current reader/writer
        let cache =
            if let Some(recent_snapshot) = self.caches.iter().next_back().map(|(key, _)| key) {
                self.caches.peek(recent_snapshot).unwrap().clone()
            } else {
                // If this is the first time, use default
                B512Map::with_capacity(10)
            };

        self.caches.put(snapshot_id, cache);
        self.caches.get_mut(&snapshot_id).unwrap()
    }

    /// Save a writer transaction's cache by promoting it to most recently used
    pub fn save_cache(&mut self, snapshot_id: SnapshotId) {
        if self.caches.contains(&snapshot_id) {
            self.caches.promote(&snapshot_id);
        }
    }

    /// Clear a specific snapshot's cache and remove it from the LRU cache
    pub fn clear_cache(&mut self, snapshot_id: SnapshotId) {
        if let Some(cache) = self.caches.get_mut(&snapshot_id) {
            cache.clear();
            self.caches.pop(&snapshot_id);
        }
    }
}

impl Default for CacheManager {
    fn default() -> Self {
        Self { max_size: 100, caches: LruCache::new(NonZeroUsize::new(100).unwrap()) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::path::AddressPath;
    use alloy_primitives::address;

    #[test]
    fn test_cache_manager_creation() {
        let cache_manager = CacheManager::new();
        assert!(cache_manager.caches.is_empty());
    }

    #[test]
    fn test_get_cache_creates_new() {
        let mut cache_manager = CacheManager::new();
        let snapshot_id = 1;

        let _ = cache_manager.get_cache(snapshot_id);
        // Verify the cache was stored
        assert!(cache_manager.caches.contains(&snapshot_id));
    }

    #[test]
    fn test_get_cache_reuses_existing() {
        let mut cache_manager = CacheManager::new();
        let snapshot_id = 1;
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let address_path = AddressPath::for_address(address);
        let nibbles = address_path.to_nibbles();
        let cache_entry = (PageId::new(100).unwrap(), 5);

        // First time create cache and entry
        {
            let cache = cache_manager.get_cache(snapshot_id);
            cache.insert(nibbles, cache_entry);
        }

        // Retrieve entry with existing cache
        {
            let cache = cache_manager.get_cache(snapshot_id);
            assert_eq!(cache.get(nibbles), Some(cache_entry));
        }
    }

    #[test]
    fn test_save_cache() {
        let mut cache_manager = CacheManager::new();
        let snapshot_id = 1;
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let address_path = AddressPath::for_address(address);
        let nibbles = address_path.to_nibbles();
        let cache_entry = (PageId::new(100).unwrap(), 5);

        // Create and populate cache
        {
            let cache = cache_manager.get_cache(snapshot_id);
            cache.insert(nibbles, cache_entry);
        }

        // Save and promote it to most recently used
        cache_manager.save_cache(snapshot_id);

        // Even though this is operating on a different snapshot,
        // we can use the most recent copy and go from there
        let new_snapshot_id = 2;
        let new_cache = cache_manager.get_cache(new_snapshot_id);
        assert_eq!(new_cache.get(nibbles), Some(cache_entry));
    }

    #[test]
    fn test_clear_cache() {
        let mut cache_manager = CacheManager::new();
        let snapshot_id = 1;
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let address_path = AddressPath::for_address(address);
        let nibbles = address_path.to_nibbles();
        let cache_entry = (PageId::new(100).unwrap(), 5);

        // Create and populate cache
        {
            let cache = cache_manager.get_cache(snapshot_id);
            cache.insert(nibbles, cache_entry);
            assert_eq!(cache.get(nibbles), Some(cache_entry));
        }

        // Clear the cache
        cache_manager.clear_cache(snapshot_id);

        // Cache should be empty but still exist
        let cache = cache_manager.get_cache(snapshot_id);
        assert_eq!(cache.get(nibbles), None);
    }

    #[test]
    fn test_clear_cache_nonexistent() {
        let mut cache_manager = CacheManager::new();
        let snapshot_id = 1;

        // Clear non-existent cache - should not panic
        cache_manager.clear_cache(snapshot_id);

        // Should still be empty
        assert!(cache_manager.caches.is_empty());
    }
}
