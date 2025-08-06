use std::{
    collections::{HashMap, VecDeque},
    hash::Hash,
    sync::{Arc, Mutex},
};

/// A node in the doubly-linked list for LRU tracking
#[derive(Debug)]
struct LruNode<K> {
    key: K,
    prev: Option<Box<LruNode<K>>>,
    next: Option<Box<LruNode<K>>>,
}

/// Thread-safe LRU cache for page eviction
/// Uses HashMap + doubly-linked list for O(1) operations
#[derive(Debug)]
pub struct LruReplacer<K>
where
    K: Clone + Eq + Hash,
{
    inner: Arc<Mutex<LruInner<K>>>,
}

#[derive(Debug)]
struct LruInner<K>
where
    K: Clone + Eq + Hash,
{
    capacity: usize,
    // Map from key to position in linked list
    map: HashMap<K, *mut LruNode<K>>,
    // Doubly-linked list for LRU ordering
    head: Option<Box<LruNode<K>>>,
    tail: Option<*mut LruNode<K>>,
    // Set of pinned items that cannot be evicted
    pinned: HashMap<K, u32>, // K -> pin_count
}

impl<K> LruReplacer<K>
where
    K: Clone + Eq + Hash + std::fmt::Debug,
{
    /// Creates a new LRU replacer with the given capacity
    pub fn new(capacity: usize) -> Self {
        Self {
            inner: Arc::new(Mutex::new(LruInner {
                capacity,
                map: HashMap::new(),
                head: None,
                tail: None,
                pinned: HashMap::new(),
            })),
        }
    }

    /// Evicts the least recently used item that is not pinned
    /// Returns the evicted item, or None if no item can be evicted
    pub fn evict(&self) -> Option<K> {
        let mut inner = self.inner.lock().unwrap();
        inner.evict_lru()
    }

    /// Marks an item as recently accessed, moving it to the front
    /// If the item doesn't exist, adds it to the front
    pub fn touch(&self, key: K) -> Result<(), String> {
        let mut inner = self.inner.lock().unwrap();

        if inner.map.contains_key(&key) {
            inner.move_to_front(&key);
        } else {
            inner.add_to_front(key)?;
        }
        Ok(())
    }

    /// Pins an item, preventing it from being evicted
    /// Pinned items are removed from the LRU list
    pub fn pin(&self, key: K) -> Result<(), String> {
        let mut inner = self.inner.lock().unwrap();

        // Increase pin count
        *inner.pinned.entry(key.clone()).or_insert(0) += 1;

        // Remove from LRU list if it was there
        if inner.map.contains_key(&key) {
            inner.remove_from_list(&key);
        }

        Ok(())
    }

    /// Unpins an item, making it eligible for eviction again
    /// Adds it back to the front of the LRU list
    pub fn unpin(&self, key: K) -> Result<(), String> {
        let mut inner = self.inner.lock().unwrap();

        if let Some(pin_count) = inner.pinned.get_mut(&key) {
            *pin_count -= 1;
            if *pin_count == 0 {
                inner.pinned.remove(&key);
                // Add back to LRU list at the front (most recently used)
                inner.add_to_front(key)?;
            }
            Ok(())
        } else {
            Err(format!("Attempted to unpin non-pinned item: {:?}", key))
        }
    }

    /// Removes an item completely from the replacer
    pub fn remove(&self, key: &K) -> Result<(), String> {
        let mut inner = self.inner.lock().unwrap();

        // Check if item is pinned
        if inner.pinned.contains_key(key) {
            return Err(format!("Cannot remove pinned item: {:?}", key));
        }

        inner.remove_from_list(key);
        Ok(())
    }

    /// Returns the current size of the LRU list (excluding pinned items)
    pub fn size(&self) -> usize {
        let inner = self.inner.lock().unwrap();
        inner.map.len()
    }

    /// Returns the capacity of the replacer
    pub fn capacity(&self) -> usize {
        let inner = self.inner.lock().unwrap();
        inner.capacity
    }

    /// Checks if an item exists in the replacer (either in LRU list or pinned)
    pub fn contains(&self, key: &K) -> bool {
        let inner = self.inner.lock().unwrap();
        inner.map.contains_key(key) || inner.pinned.contains_key(key)
    }
}

impl<K> LruInner<K>
where
    K: Clone + Eq + Hash + std::fmt::Debug,
{
    /// Evicts the least recently used unpinned item
    fn evict_lru(&mut self) -> Option<K> {
        // Find the tail (least recently used)
        let tail_ptr = self.tail?;
        let key = unsafe { &(*tail_ptr).key }.clone();

        // Remove from list
        self.remove_from_list(&key);
        Some(key)
    }

    /// Adds an item to the front of the list (most recently used position)
    fn add_to_front(&mut self, key: K) -> Result<(), String> {
        if self.map.len() >= self.capacity {
            // Try to evict something first
            if self.evict_lru().is_none() {
                return Err("Cache is full and no items can be evicted".to_string());
            }
        }

        let new_node = Box::new(LruNode { key: key.clone(), prev: None, next: self.head.take() });

        let new_node_ptr = Box::into_raw(new_node);

        // Update the old head's prev pointer
        if let Some(ref mut old_head) = unsafe { (*new_node_ptr).next.as_mut() } {
            old_head.prev = Some(unsafe { Box::from_raw(new_node_ptr) });
            // Put the node back as raw pointer
            Box::into_raw(old_head.prev.take().unwrap());
        } else {
            // This is the first node, so it's also the tail
            self.tail = Some(new_node_ptr);
        }

        // Update head
        self.head = Some(unsafe { Box::from_raw(new_node_ptr) });
        self.map.insert(key, new_node_ptr);

        Ok(())
    }

    /// Moves an existing item to the front of the list
    fn move_to_front(&mut self, key: &K) {
        if let Some(&node_ptr) = self.map.get(key) {
            // Remove from current position
            self.remove_node(node_ptr);

            // Add to front
            unsafe {
                (*node_ptr).prev = None;
                (*node_ptr).next = self.head.take();

                if let Some(ref mut old_head) = (*node_ptr).next.as_mut() {
                    old_head.prev = Some(Box::from_raw(node_ptr));
                    Box::into_raw(old_head.prev.take().unwrap());
                } else {
                    self.tail = Some(node_ptr);
                }

                self.head = Some(Box::from_raw(node_ptr));
            }
        }
    }

    /// Removes an item from the list and map
    fn remove_from_list(&mut self, key: &K) {
        if let Some(node_ptr) = self.map.remove(key) {
            self.remove_node(node_ptr);
            // Clean up the node
            unsafe {
                drop(Box::from_raw(node_ptr));
            }
        }
    }

    /// Removes a node from the linked list structure
    fn remove_node(&mut self, node_ptr: *mut LruNode<K>) {
        unsafe {
            let node = &mut *node_ptr;

            // Update prev node's next pointer
            if let Some(ref mut prev_box) = node.prev {
                prev_box.next = node.next.take();
            } else {
                // This was the head
                self.head = node.next.take();
            }

            // Update next node's prev pointer
            if let Some(ref mut next_box) = node.next {
                next_box.prev = node.prev.take();
            } else {
                // This was the tail
                self.tail = if let Some(ref prev_box) = node.prev {
                    Some(prev_box.as_ref() as *const LruNode<K> as *mut LruNode<K>)
                } else {
                    None
                };
            }
        }
    }
}

// Implement Clone for LruReplacer to allow sharing between threads
impl<K> Clone for LruReplacer<K>
where
    K: Clone + Eq + Hash,
{
    fn clone(&self) -> Self {
        Self { inner: Arc::clone(&self.inner) }
    }
}

// Ensure Send + Sync for thread safety
unsafe impl<K> Send for LruReplacer<K> where K: Clone + Eq + Hash + Send {}
unsafe impl<K> Sync for LruReplacer<K> where K: Clone + Eq + Hash + Send {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_lru_operations() {
        let lru = LruReplacer::new(3);

        // Add items
        lru.touch(1).unwrap();
        lru.touch(2).unwrap();
        lru.touch(3).unwrap();

        assert_eq!(lru.size(), 3);

        // Access item 1 (should move to front)
        lru.touch(1).unwrap();

        // Add item 4 (should evict least recently used)
        lru.touch(4).unwrap();

        // Item 2 should have been evicted
        assert_eq!(lru.size(), 3);
    }

    #[test]
    fn test_eviction() {
        let lru = LruReplacer::new(2);

        lru.touch(1).unwrap();
        lru.touch(2).unwrap();

        // Evict should return least recently used (1)
        assert_eq!(lru.evict(), Some(1));
        assert_eq!(lru.size(), 1);

        // Evict should return the remaining item (2)
        assert_eq!(lru.evict(), Some(2));
        assert_eq!(lru.size(), 0);

        // No more items to evict
        assert_eq!(lru.evict(), None);
    }

    #[test]
    fn test_pin_unpin() {
        let lru = LruReplacer::new(2);

        lru.touch(1).unwrap();
        lru.touch(2).unwrap();

        // Pin item 1
        lru.pin(1).unwrap();

        // Try to evict - should get item 2 since 1 is pinned
        assert_eq!(lru.evict(), Some(2));

        // No more unpinned items
        assert_eq!(lru.evict(), None);

        // Unpin item 1
        lru.unpin(1).unwrap();

        // Now item 1 can be evicted
        assert_eq!(lru.evict(), Some(1));
    }

    #[test]
    fn test_contains() {
        let lru = LruReplacer::new(2);

        lru.touch(1).unwrap();
        assert!(lru.contains(&1));
        assert!(!lru.contains(&2));

        lru.pin(1).unwrap();
        assert!(lru.contains(&1)); // Still contains pinned items

        lru.remove(&1).unwrap_err(); // Can't remove pinned items

        lru.unpin(1).unwrap();
        lru.remove(&1).unwrap();
        assert!(!lru.contains(&1));
    }
}
