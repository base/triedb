use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};

use parking_lot::Mutex;

use crate::page::manager::buffer_pool::FrameId;

struct FrameState {
    // The Second Chance bit
    ref_bit: AtomicBool,
    // If true, this frame cannot be evicted
    pin: AtomicBool,
}

pub struct ClockReplacer {
    frames: Vec<FrameState>,
    hand: Mutex<usize>,
}

impl ClockReplacer {
    pub fn new(num_frames: usize) -> Self {
        let mut frames = Vec::with_capacity(num_frames);
        for _ in 0..num_frames {
            frames
                .push(FrameState { ref_bit: AtomicBool::new(false), pin: AtomicBool::new(false) });
        }

        ClockReplacer { frames, hand: Mutex::new(0) }
    }

    #[inline]
    pub fn pin(&self, frame_id: FrameId) {
        // Safety check
        if frame_id.as_usize() >= self.frames.len() {
            return;
        }

        let frame = &self.frames[frame_id.as_usize()];
        // First increment pin count
        frame.pin.store(true, Ordering::SeqCst);
        // Then set usage bit to true (give it a second chance)
        frame.ref_bit.store(true, Ordering::SeqCst);
    }

    pub fn unpin(&self, frame_id: FrameId) {
        if frame_id.as_usize() >= self.frames.len() {
            return;
        }

        let frame = &self.frames[frame_id.as_usize()];
        frame.pin.store(false, Ordering::SeqCst);
    }

    // Find a frame to evict
    pub fn victim(&self) -> Option<FrameId> {
        let mut hand = self.hand.lock();
        let num_frames = self.frames.len();

        for _ in 0..(num_frames * 3) {
            let current_idx = *hand;
            let frame = &self.frames[current_idx];

            // Move hand forward for next iteration
            *hand = (*hand + 1) % num_frames;

            let current_pins = frame.pin.load(Ordering::SeqCst);
            if current_pins {
                // This page is being used. Cannot evict. Skip it.
                continue;
            }
            // Check reference bit: swap atomically returns old value and sets to false
            if frame.ref_bit.swap(false, Ordering::SeqCst) {
                // Had a second chance (was true, now set to false)
                continue;
            }

            return Some(FrameId::from_usize(current_idx));
        }

        // If get here, literally every single frame is Pinned. The buffer pool is exhausted.
        None
    }

    // Find a frame to evict and pin it
    pub fn victim_and_pin<F>(&self, cleanup: F) -> Option<FrameId>
    where
        F: FnOnce(FrameId),
    {
        let mut hand = self.hand.lock();
        let num_frames = self.frames.len();

        for _ in 0..(num_frames * 3) {
            let current_idx = *hand;
            let frame = &self.frames[current_idx];

            // Move hand forward for next iteration
            *hand = (*hand + 1) % num_frames;

            let current_pins = frame.pin.load(Ordering::SeqCst);
            if current_pins {
                // This page is being used. Cannot evict. Skip it.
                continue;
            }
            // Check reference bit: swap atomically returns old value and sets to false
            if frame.ref_bit.swap(false, Ordering::SeqCst) {
                // Had a second chance (was true, now set to false)
                continue;
            }

            // Pin the frame
            let frame = &self.frames[current_idx];
            frame.pin.store(true, Ordering::SeqCst);
            frame.ref_bit.store(true, Ordering::SeqCst);
            let frame_id = FrameId::from_usize(current_idx);
            cleanup(frame_id);
            return Some(frame_id);
        }

        // If get here, literally every single frame is Pinned. The buffer pool is exhausted.
        None
    }

    #[cfg(test)]
    fn count_pinned(&self) -> usize {
        self.frames.iter().filter(|f| f.pin.load(Ordering::SeqCst)).count()
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
            assert_eq!(r.victim(), Some(FrameId::from_usize(i)));
            r.pin(FrameId::from_usize(i));
        });
        assert_eq!(r.victim(), None);

        r.unpin(FrameId::from_usize(4));
        assert_eq!(r.victim(), Some(FrameId::from_usize(4)));
    }
}
