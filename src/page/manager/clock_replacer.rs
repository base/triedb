use std::sync::atomic::{AtomicU8, Ordering};

use parking_lot::Mutex;

use crate::page::manager::buffer_pool::FrameId;

struct FrameState {
    // Bit 0: pin (If true, this frame cannot be evicted)
    // Bit 1: ref_bit (Second Chance bit)
    state: AtomicU8,
}

pub(crate) struct ClockReplacer {
    frames: Vec<FrameState>,
    hand: Mutex<usize>,
}

impl ClockReplacer {
    pub(super) fn new(num_frames: usize) -> Self {
        let mut frames = Vec::with_capacity(num_frames);
        for _ in 0..num_frames {
            frames.push(FrameState { state: AtomicU8::new(0) });
        }

        ClockReplacer { frames, hand: Mutex::new(0) }
    }

    #[inline]
    pub(super) fn pin(&self, frame_id: FrameId) {
        // Safety check
        if frame_id.as_usize() >= self.frames.len() {
            return;
        }

        let frame = &self.frames[frame_id.as_usize()];
        // Set both pin (bit 0) and ref_bit (bit 1) to true
        frame.state.store(0b11, Ordering::Relaxed);
    }

    pub(super) fn unpin(&self, frame_id: FrameId) {
        if frame_id.as_usize() >= self.frames.len() {
            return;
        }

        let frame = &self.frames[frame_id.as_usize()];
        // Clear pin bit (bit 0), keep ref_bit unchanged
        frame.state.fetch_and(0b10, Ordering::Release);
    }

    // Find a frame to evict and pin it
    pub(super) fn victim_and_pin<F>(&self, cleanup: F) -> Option<FrameId>
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
            return Some(frame_id);
        }

        // If get here, literally every single frame is Pinned. The buffer pool is exhausted.
        None
    }

    #[cfg(test)]
    pub(super) fn count_pinned(&self) -> usize {
        self.frames.iter().filter(|f| (f.state.load(Ordering::SeqCst) & 0b01) != 0).count()
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
