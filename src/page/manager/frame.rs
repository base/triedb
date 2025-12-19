use crate::{
    page::{
        state::{PageState, RawPageState},
        Page, PageError, PageId, PageManagerOptions, PageMut,
    },
    snapshot::SnapshotId,
};
use parking_lot::Mutex;
use std::sync::atomic::{AtomicU32, Ordering};

#[derive(Debug)]
pub(crate) struct Frame {
    ptr: *mut [u8; Page::SIZE],
    page_id: AtomicU32, // 0 means None, otherwise it's the page_id
    state: AtomicU32,   // Bit 0: pin (If true, this frame cannot be evicted)
                        // Bit 1: ref_bit (Second Chance bit)
}

impl Clone for Frame {
    fn clone(&self) -> Self {
        Frame {
            ptr: self.ptr,
            page_id: AtomicU32::new(self.page_id.load(Ordering::SeqCst)),
            state: AtomicU32::new(self.state.load(Ordering::SeqCst)),
        }
    }
}

impl Frame {
    // Unpin the frame if the page is not dirty.
    // If the page is in dirty state, returns false.
    #[inline]
    pub(crate) fn unpin(&self) -> bool {
        let is_dirty = unsafe { PageState::is_dirty(self.ptr.cast()) };

        if is_dirty {
            return false;
        }
        // Clear pin bit (bit 0), keep ref_bit (bit 1) unchanged
        self.state.fetch_and(0b10, Ordering::Release);
        true
    }

    #[inline]
    pub(crate) fn pin(&self) {
        // Set both pin (bit 0) and ref_bit (bit 1) to true
        self.state.store(0b11, Ordering::Release);
    }
}

// SAFETY: Frame contains a pointer to heap-allocated memory that we own exclusively.
// The memory is allocated via Box and we manage its lifetime, so it's safe to send
// between threads.
unsafe impl Send for Frame {}
unsafe impl Sync for Frame {}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub(crate) struct FrameId(u32);

impl FrameId {
    #[inline(always)]
    pub(crate) const fn as_usize(&self) -> usize {
        self.0 as usize
    }

    #[inline]
    pub(crate) const fn from_usize(value: usize) -> Self {
        FrameId(value as u32)
    }
}

pub(crate) struct Frames {
    inner: Vec<Frame>,
    hand: Mutex<usize>,
}

impl Frames {
    pub(crate) fn allocate(num_frames: usize) -> Self {
        let mut frames = Vec::with_capacity(num_frames);
        (0..num_frames).into_iter().for_each(|_| {
            let boxed_array = Box::new([0; Page::SIZE]);
            let ptr = Box::into_raw(boxed_array);
            frames.push(Frame { ptr, page_id: AtomicU32::new(0), state: AtomicU32::new(0) });
        });
        Self { inner: frames, hand: Mutex::new(0) }
    }

    #[inline(always)]
    pub(crate) fn get(&self, frame_id: FrameId) -> &Frame {
        &self.inner[frame_id.0 as usize]
    }

    // Unpin the frame if the occupied page is not dirty.
    // If the page is in dirty state, returns false.
    pub(crate) fn unpin(&self, frame_id: FrameId) -> bool {
        let frame = self.get(frame_id);
        frame.unpin()
    }

    // Find a frame to be evicted, also pin that frame and running cleanup F function.
    pub(crate) fn victim_and_pin<F>(&self, cleanup: F) -> Option<(FrameId, &Frame)>
    where
        F: FnOnce(FrameId),
    {
        let mut hand = self.hand.lock();
        let num_frames = self.inner.len();

        for _ in 0..(num_frames * 3) {
            let current_idx = *hand;
            let frame = &self.inner[current_idx];

            // Move hand forward for next iteration
            *hand = (*hand + 1) % num_frames;

            // Check if pin bit (bit 0) is set
            let current_state = frame.state.load(Ordering::Relaxed);
            if (current_state & 0b01) != 0 {
                // This page is being used. Cannot evict. Skip it.
                continue;
            }
            // Check reference bit (bit 1): swap atomically returns old value and sets to false
            let old_state = frame.state.swap(current_state & 0b01, Ordering::Relaxed);
            if (old_state & 0b10) != 0 {
                // Had a second chance (ref_bit was true, now set to false)
                continue;
            }

            // Pin the frame: set both pin (bit 0) and ref_bit (bit 1) to true
            frame.state.store(0b11, Ordering::Relaxed);
            let frame_id = FrameId::from_usize(current_idx);
            cleanup(frame_id);
            return Some((frame_id, frame));
        }

        // If get here, literally every single frame is pinned. The buffer pool is exhausted.
        None
    }

    #[cfg(test)]
    fn count_pinned(&self) -> usize {
        self.inner.iter().filter(|i| (i.state.load(Ordering::SeqCst) & 0b01) != 0).count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pin() {
        let r = ClockReplacer::new(5);
        r.pin(FrameId::from_usize(0));
        assert_eq!(r.count_pinned(), 1);
        r.pin(FrameId::from_usize(0));
        assert_eq!(r.count_pinned(), 1);
        r.pin(FrameId::from_usize(4));
        assert_eq!(r.count_pinned(), 2);
    }

    #[test]
    fn test_upin() {
        let r = ClockReplacer::new(5);
        r.pin(FrameId::from_usize(0));
        r.pin(FrameId::from_usize(1));
        r.pin(FrameId::from_usize(1));
        r.pin(FrameId::from_usize(2));
        assert_eq!(r.count_pinned(), 3);

        r.unpin(FrameId::from_usize(2));
        assert_eq!(r.count_pinned(), 2);

        r.unpin(FrameId::from_usize(1));
        assert_eq!(r.count_pinned(), 1);
        r.unpin(FrameId::from_usize(1));
        assert_eq!(r.count_pinned(), 1);
    }

    #[test]
    fn test_evict() {
        let r = ClockReplacer::new(5);
        (0..5).for_each(|i| {
            assert_eq!(r.victim_and_pin(|_| {}), Some(FrameId::from_usize(i)));
            r.pin(FrameId::from_usize(i));
        });
        assert_eq!(r.victim_and_pin(|_| {}), None);

        r.unpin(FrameId::from_usize(4));
        assert_eq!(r.victim_and_pin(|_| {}), Some(FrameId::from_usize(4)));
    }
}

