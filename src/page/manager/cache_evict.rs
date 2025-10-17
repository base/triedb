use std::{
    collections::HashMap,
    fmt, mem,
    num::NonZeroUsize,
    ptr::{self, NonNull},
};

use core::hash::{BuildHasher, Hash, Hasher};

use evict::{EvictResult, EvictionPolicy, LruReplacer};
use parking_lot::Mutex;

use crate::page::{manager::buffer_pool::FrameId, PageId};

// TODO: Temporarily use LruReplacer as the eviction policy, replace with a better eviction policy
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
            lru_replacer: LruReplacer::new(capacity),
            read_frames: Mutex::new(Vec::with_capacity(capacity)),
            update_frames: Mutex::new(Vec::with_capacity(capacity)),
            new_frames: Mutex::new(Vec::with_capacity(capacity)),
        }
    }

    pub(crate) fn evict(&self) -> Option<PageId> {
        self.lru_replacer.evict()
    }

    pub(crate) fn touch(&self, page_id: PageId) -> EvictResult<(), PageId> {
        self.lru_replacer.touch(page_id)
    }

    pub(crate) fn pin_read(&self, page_id: PageId) -> EvictResult<(), PageId> {
        self.read_frames.lock().push(page_id);
        self.lru_replacer.pin(page_id)
    }

    pub(crate) fn pin_write_update_page(
        &self,
        frame_id: FrameId,
        page_id: PageId,
    ) -> EvictResult<(), PageId> {
        if let Some((_, first_page_id)) = self.new_frames.lock().first() {
            if page_id.as_u32() < first_page_id.as_u32() {
                self.update_frames.lock().push((frame_id, page_id));
            }
        } else {
            self.update_frames.lock().push((frame_id, page_id));
        }

        self.lru_replacer.pin(page_id)
    }

    pub(crate) fn pin_write_new_page(
        &self,
        frame_id: FrameId,
        page_id: PageId,
    ) -> EvictResult<(), PageId> {
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

        self.lru_replacer.pin(page_id)
    }

    pub(crate) fn unpin(&self, page_id: PageId) -> EvictResult<(), PageId> {
        self.lru_replacer.unpin(page_id)
    }
}

// LRU implementation inspired from https://github.com/jeromefroe/lru-rs/blob/master/src/lib.rs
// Struct used to hold a reference to a key
struct KeyRef<K> {
    k: *const K,
}

impl<K: Hash> Hash for KeyRef<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        unsafe { (*self.k).hash(state) }
    }
}

impl<K: PartialEq> PartialEq for KeyRef<K> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { (*self.k).eq(&*other.k) }
    }
}

// Eq extends PartialEq
impl<K: Eq> Eq for KeyRef<K> {}

struct LRUEntry<K> {
    key: mem::MaybeUninit<K>,
    prev: *mut LRUEntry<K>,
    next: *mut LRUEntry<K>,
}

impl<K> LRUEntry<K> {
    fn new(key: K) -> Self {
        LRUEntry { key: mem::MaybeUninit::new(key), prev: ptr::null_mut(), next: ptr::null_mut() }
    }

    fn new_sigil() -> Self {
        LRUEntry { key: mem::MaybeUninit::uninit(), prev: ptr::null_mut(), next: ptr::null_mut() }
    }
}

type DefaultHasher = std::collections::hash_map::RandomState;

#[derive(Debug)]
enum Error {
    CacheIsFull,
}

// An LRU cache
struct TLruReplacer<K, S = DefaultHasher> {
    map: HashMap<KeyRef<K>, NonNull<LRUEntry<K>>, S>,
    cap: NonZeroUsize,
    // head and tail are sigil nodes to facilitate inserting entries
    head: *mut LRUEntry<K>,
    tail: *mut LRUEntry<K>,
}

impl<K: Hash + Eq> TLruReplacer<K> {
    pub fn new(cap: NonZeroUsize) -> Self {
        Self::construct(cap, HashMap::with_capacity(cap.get()))
    }
}

impl<K: Hash + Eq, S: BuildHasher> TLruReplacer<K, S> {
    fn construct(cap: NonZeroUsize, map: HashMap<KeyRef<K>, NonNull<LRUEntry<K>>, S>) -> Self {
        let lru_replacer = TLruReplacer {
            map,
            cap,
            head: Box::into_raw(Box::new(LRUEntry::new_sigil())),
            tail: Box::into_raw(Box::new(LRUEntry::new_sigil())),
        };

        unsafe {
            (*lru_replacer.head).next = lru_replacer.tail;
            (*lru_replacer.tail).prev = lru_replacer.head;
        }

        lru_replacer
    }

    fn is_empty(&self) -> bool {
        todo!()
    }

    /// Touches a key in replacer. This shifts the key to head of LRU
    fn touch(&mut self, k: K) -> Result<(), Error> {
        let node_ref = self.map.get_mut(&KeyRef { k: &k });

        match node_ref {
            Some(node_ref) => {
                // If the key is already in the cache, just move it to the front of the list
                let node_ptr = node_ref.as_ptr();
                self.detach(node_ptr);
                self.attach(node_ptr);
            }
            None => {}
        }
    }

    fn peak(&self) -> Option<K> {
        todo!()
    }

    fn pin(&self, k: K) -> Result<bool, Error> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use crate::page::manager::cache_evict::TLruReplacer;

    #[test]
    fn test_touch_and_evict() {
        let mut cache = TLruReplacer::new(NonZeroUsize::new(2).unwrap());
        assert!(cache.is_empty());

        assert_eq!(cache.touch(12), None);
        assert_eq!(cache.touch(13), None);
        assert_eq!(cache.len(), 2);
        assert!(!cache.is_empty());
        assert_eq!(cache.peak(), 13);
        assert_eq!(cache.touch(12), None);
        assert_eq!(cache.peak(), 12);

        assert_eq!(cache.evict(), 12);
        assert_eq!(cache.peak(), 13);
        assert_eq!(cache.len(), 1);

        assert_eq!(cache.evict(), 13);
        assert_eq!(cache.evict(), None);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_pin() {
        let mut cache = TLruReplacer::new(NonZeroUsize::new(2).unwrap());
        assert_eq!(cache.touch(12), None);
        assert_eq!(cache.touch(13), None);
        assert_eq!(cache.pin(12), None);
        assert_eq!(cache.peak(), Some(13));
        assert_eq!(cache.len(), 1);
    }
}
