use std::collections::HashMap;

use crate::{context::B512Map, page::PageId, snapshot::SnapshotId};


/// A cache manager that maintains the account-location cache centrally instead of
/// per-transaction. Since the reader and writer transactions can be operating on different 
/// versions of the trie simultaneously, the cache would need to be scoped to a single snapshot 
/// version. Ideally when a writer transaction is committed, we should save its cache and use 
/// this (or a copy of it) for new readers and writers.
#[derive(Debug, Clone)]
pub struct CacheManager {
    /// Cache by snapshotID
    snapshot_caches: HashMap<SnapshotId, B512Map<(PageId, u8)>>,
    /// The latest committed cache (used for new readers/writers)
    latest_committed_cache: Option<B512Map<(PageId, u8)>>,
}

impl CacheManager {
    pub fn new() -> Self {
        Self::default()
    }

    /// Get/add a per-transaction cache for current snapshotID
    /// It uses the latest committed cache if available
    pub fn get_cache(&mut self, snapshot_id: SnapshotId) -> &mut B512Map<(PageId, u8)> {
        // If cache already exists for this snapshot, return it
        if self.snapshot_caches.contains_key(&snapshot_id) {
            return self.snapshot_caches.get_mut(&snapshot_id).unwrap();
        }
        
        // Create new cache, starting from latest committed cache if available
        let new_cache = if let Some(ref committed_cache) = self.latest_committed_cache {
            committed_cache.clone()
        } else {
            B512Map::with_capacity(10)
        };
        
        self.snapshot_caches.insert(snapshot_id, new_cache);
        self.snapshot_caches.get_mut(&snapshot_id).unwrap()
    }

    /// Save a writer transaction's cache and use this for new readers/writers
    pub fn save_cache(&mut self, snapshot_id: SnapshotId) {
        if let Some(cache) = self.snapshot_caches.get(&snapshot_id) {
            self.latest_committed_cache = Some(cache.clone());
        }
    }

    /// Clear a specific snapshot's cache
    pub fn clear_cache(&mut self, snapshot_id: SnapshotId) {
        if let Some(cache) = self.snapshot_caches.get_mut(&snapshot_id) {
            cache.clear();
        }
    }
}

impl Default for CacheManager {
    fn default() -> Self {
        Self {
            snapshot_caches: HashMap::new(),
            latest_committed_cache: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::address;
    use crate::path::AddressPath;

    #[test]
    fn test_cache_manager_creation() {
        let cache_manager = CacheManager::new();
        assert!(cache_manager.snapshot_caches.is_empty());
        assert!(cache_manager.latest_committed_cache.is_none());
    }

    #[test]
    fn test_get_cache_creates_new() {
        let mut cache_manager = CacheManager::new();
        let snapshot_id = 1;
        
        let _ = cache_manager.get_cache(snapshot_id);
        // Verify the cache was stored
        assert!(cache_manager.snapshot_caches.contains_key(&snapshot_id));
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
        
        // Initially no committed cache
        assert!(cache_manager.latest_committed_cache.is_none());
        
        // Commit the cache
        cache_manager.save_cache(snapshot_id);
        
        // Should now have committed cache
        assert!(cache_manager.latest_committed_cache.is_some());
        let committed_cache = cache_manager.latest_committed_cache.as_ref().unwrap();
        assert_eq!(committed_cache.get(nibbles), Some(cache_entry));
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
        assert!(cache_manager.snapshot_caches.is_empty());
    }
}

