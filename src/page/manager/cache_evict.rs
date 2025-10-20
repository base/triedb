use std::{
    fmt, mem,
    num::NonZeroUsize,
    ptr::{self, NonNull},
};

use core::hash::{Hash, Hasher};
use dashmap::DashMap;

use parking_lot::{Mutex, RwLock};

use crate::page::{manager::buffer_pool::FrameId, PageId};

pub(crate) struct CacheEvict {
    lru_replacer: LruReplacer<PageId>,
    read_frames: Mutex<Vec<PageId>>,
    pub(crate) update_frames: Mutex<Vec<(FrameId, PageId)>>,
    pub(crate) new_frames: Mutex<Vec<(FrameId, PageId)>>,
}

impl fmt::Debug for CacheEvict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CacheEvict")
    }
}

impl CacheEvict {
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            lru_replacer: LruReplacer::new(NonZeroUsize::new(capacity).unwrap()),
            read_frames: Mutex::new(Vec::with_capacity(capacity)),
            update_frames: Mutex::new(Vec::with_capacity(capacity)),
            new_frames: Mutex::new(Vec::with_capacity(capacity)),
        }
    }

    pub(crate) fn evict(&self) -> Option<PageId> {
        self.lru_replacer.evict().copied()
    }

    // pub(crate) fn touch(&self, page_id: PageId) -> EvictResult<(), PageId> {
    //     self.lru_replacer.touch(page_id)
    // }

    /// Returns true if page_id was in the cache list.
    pub(crate) fn pin_read(&self, page_id: PageId) {
        self.read_frames.lock().push(page_id);
        self.lru_replacer.remove(&page_id);
    }

    pub(crate) fn pin_write_update_page(&self, frame_id: FrameId, page_id: PageId) {
        if let Some((_, first_page_id)) = self.new_frames.lock().first() {
            if page_id.as_u32() < first_page_id.as_u32() {
                self.update_frames.lock().push((frame_id, page_id));
            }
        } else {
            self.update_frames.lock().push((frame_id, page_id));
        }

        self.lru_replacer.remove(&page_id);
    }

    pub(crate) fn pin_write_new_page(&self, frame_id: FrameId, page_id: PageId) {
        let mut new_frames = self.new_frames.lock();
        if let Some((_, last_page_id)) = new_frames.last() {
            debug_assert!(
                last_page_id.as_u32() + 1 == page_id,
                "page_id: {:?}, last_page_id: {:?}",
                page_id,
                last_page_id
            );
        }
        new_frames.push((frame_id, page_id));

        self.lru_replacer.remove(&page_id);
    }

    pub(crate) fn unpin(&self, page_id: PageId) -> Result<(), Error> {
        self.lru_replacer.touch(page_id)
    }
}

// LRU implementation inspired from https://github.com/jeromefroe/lru-rs/blob/master/src/lib.rs
// Struct used to hold a reference to a key

struct LruEntry<K> {
    prev: *mut LruEntry<K>,
    next: *mut LruEntry<K>,
    key: mem::MaybeUninit<K>,
}

// // SAFETY: LruEntry<K> contains raw pointers that form a doubly-linked list.
// // These pointers are all heap-allocated and managed by LruReplacer.
// // Access to the linked list is synchronized through the RwLock in LruReplacer.
// // It is safe to send LruEntry<K> across threads when K is Send.
// unsafe impl<K: Send> Send for LruEntry<K> {}

impl<K> LruEntry<K> {
    fn new(key: K) -> Self {
        LruEntry { key: mem::MaybeUninit::new(key), prev: ptr::null_mut(), next: ptr::null_mut() }
    }

    fn new_sigil() -> Self {
        LruEntry { key: mem::MaybeUninit::uninit(), prev: ptr::null_mut(), next: ptr::null_mut() }
    }
}

type DefaultHasher = std::collections::hash_map::RandomState;

#[derive(Debug, PartialEq, Eq)]
enum Error {
    CacheIsFull,
}

struct Terminals<K> {
    head: *mut LruEntry<K>,
    tail: *mut LruEntry<K>,
}

// // SAFETY: Terminals<K> contains raw pointers to heap-allocated LruEntry<K> nodes.
// // These pointers are owned by LruReplacer and access is synchronized via RwLock.
// // It is safe to send Terminals<K> across threads when K is Send.
unsafe impl<K: Send> Send for Terminals<K> {}

// An LRU cache
struct LruReplacer<K> {
    map: DashMap<K, NonNull<LruEntry<K>>>,
    cap: NonZeroUsize,
    // head and tail are sigil nodes to facilitate inserting entries
    terminals: RwLock<Terminals<K>>,
}

// Compile-time assertion to ensure that `LruReplacer` is `Send`
const _: fn() = || {
    fn assert_send<T: Send>() {}
    assert_send::<LruReplacer<u32>>();
};

impl<K: Hash + Eq + Copy> LruReplacer<K> {
    fn new(cap: NonZeroUsize) -> Self {
        Self::construct(cap, DashMap::with_capacity(cap.get()))
    }

    fn construct(cap: NonZeroUsize, map: DashMap<K, NonNull<LruEntry<K>>>) -> Self {
        let terminals: Terminals<K> = Terminals {
            head: Box::into_raw(Box::new(LruEntry::new_sigil())),
            tail: Box::into_raw(Box::new(LruEntry::new_sigil())),
        };
        unsafe {
            (*terminals.head).next = terminals.tail;
            (*terminals.tail).prev = terminals.head;
        }
        LruReplacer { map, cap, terminals: RwLock::new(terminals) }
    }

    #[inline]
    fn len(&self) -> usize {
        self.map.len()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.map.len() == 0
    }

    /// Returns the key at the tail if exist
    fn evict(&self) -> Option<&K> {
        if self.len() == 0 {
            return None;
        }
        let terminals = self.terminals.read();
        let node = unsafe { (*terminals.tail).prev };
        Self::detach(node);

        let key = unsafe { (*node).key.assume_init() };
        self.map.remove(&key);
        let key: &K = unsafe { &(*(*node).key.as_ptr()) as &K };
        Some(key)
    }

    /// Touches a key in replacer. This shifts the key to head of LRU
    pub(crate) fn touch(&self, k: K) -> Result<(), Error> {
        let node_ptr =
            if let Some(node_ref) = self.map.get_mut(&k) { Some(node_ref.as_ptr()) } else { None };

        match node_ptr {
            Some(node_ptr) => {
                // If the key is already in the cache, just move it to the head of the list
                Self::detach(node_ptr);
                self.attach(node_ptr);
                Ok(())
            }
            None => {
                // Add new key to the head of the list
                if self.map.len() >= self.cap.get() {
                    return Err(Error::CacheIsFull)
                }
                let node =
                    unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(LruEntry::new(k)))) };
                let node_ptr = node.as_ptr();
                self.attach(node_ptr);
                self.map.insert(k, node);

                Ok(())
            }
        }
    }

    /// Removes the key from the queue.
    /// Return true if the key is in the queue, false otherwise.
    fn remove(&self, k: &K) -> bool {
        let node_ref = self.map.remove(k);

        match node_ref {
            Some((_, node)) => {
                // If the key is already in the cache, just remove it
                let node_ptr = node.as_ptr();
                Self::detach(node_ptr);

                true
            }
            None => false,
        }
    }

    /// Returns the value corresponding to the least recently used item or None if the cache is
    /// empty.
    fn peek_lru(&self) -> Option<&K> {
        if self.is_empty() {
            return None;
        }
        let key;
        let terminals = self.terminals.read();
        unsafe {
            let node = (*terminals.tail).prev;
            key = &(*(*node).key.as_ptr()) as &K;
        };
        Some(key)
    }

    fn detach(node: *const LruEntry<K>) {
        unsafe {
            (*(*node).prev).next = (*node).next;
            (*(*node).next).prev = (*node).prev;
        }
    }

    fn attach(&self, node: *mut LruEntry<K>) {
        let mut terminals = self.terminals.write();
        unsafe {
            (*node).next = (*terminals.head).next;
            (*node).prev = terminals.head;
            (*terminals.head).next = node;
            (*(*node).next).prev = node;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use super::*;

    #[test]
    fn test_touch_and_evict() {
        let cache = LruReplacer::new(NonZeroUsize::new(2).unwrap());
        assert!(cache.is_empty());

        cache.touch(12).expect("should add key");
        cache.touch(13).expect("should add key");
        assert_eq!(cache.touch(14), Err(Error::CacheIsFull));
        assert_eq!(cache.len(), 2);

        assert_eq!(cache.peek_lru(), Some(&12));
        cache.touch(12).expect("should update key");
        assert_eq!(cache.peek_lru(), Some(&13));

        assert_eq!(cache.touch(14), Err(Error::CacheIsFull));

        assert_eq!(cache.evict(), Some(&13));
        assert_eq!(cache.peek_lru(), Some(&12));
        assert_eq!(cache.len(), 1);

        cache.touch(14).expect("should add key");
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.evict(), Some(&12));
        assert_eq!(cache.evict(), Some(&14));
        assert_eq!(cache.evict(), None);
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_pin() {
        let cache = LruReplacer::new(NonZeroUsize::new(2).unwrap());
        cache.touch(2).expect("should add key");
        cache.touch(3).expect("should add key");
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.remove(&2), true);
        assert_eq!(cache.remove(&20), false);
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.peek_lru(), Some(&3));
        assert_eq!(cache.remove(&3), true);
        assert_eq!(cache.len(), 0);
    }
}
