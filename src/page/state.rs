//! Structures to query and manipulate the state of pages.
//!
//! A page can be in one of 3 states:
//!
//! - **Unused:** the page contains no data and no thread is writing to it.
//! - **Occupied:** the page contains valid data and no thread is writing to it.
//! - **Dirty:** the page is being written to by a thread.
//!
//! The page state also contains the ID of the snapshot that the page belongs to. The state is
//! represented as a 64-bit number and is accessed through atomic operations. [`RawPageState`] and
//! [`RawPageStateMut`] allow fetching and changing the page state respectively.
//!
//! # Internal representation
//!
//! The state essentially consists of a 1-bit flag that encodes whether the page is dirty or not,
//! and a 63-bit snapshot ID. If the 1-bit flag is unset and the snapshot ID is all zeros, then the
//! state is interpreted as being *unused*.
//!
//! # Memory model
//!
//! `RawPageState` and `RawPageStateMut` use atomic operations to access and manipulate their
//! state, and as such use of these two structs must adhere to the [memory model for atomic
//! accesses] defined by Rust. In particular, access to the state must prevent *data races*,
//! which can happen when mixing atomic and non-atomic operations without synchronization, when
//! one of the operations is a write.
//!
//! `RawPageState` and `RawPageStateMut` are designed to hide most of the complexity of this memory
//! model, and mostly provide safe methods that can be used without introducing undefined behavior,
//! *as long as only `RawPageState` and `RawPageStateMut` are used to access the state data*.
//!
//! [memory model for atomic accesses](core::sync::atomic#memory-model-for-atomic-accesses)

use crate::snapshot::SnapshotId;
use std::{
    mem,
    sync::atomic::{AtomicU64, Ordering},
};

#[repr(transparent)]
#[derive(Debug)]
pub(super) struct RawPageState(AtomicU64);

#[repr(transparent)]
#[derive(Debug)]
pub(super) struct RawPageStateMut(AtomicU64);

impl RawPageState {
    /// Creates a `RawPageState` from a raw pointer.
    ///
    /// # Safety
    ///
    /// * `ptr` must be properly aligned.
    /// * `ptr` must be [valid] for reads for the whole lifetime `'a`.
    /// * Access to the data pointed by `ptr` must adhere to the [memory model for page state
    ///   access].
    ///
    /// [valid]: core::ptr#safety
    /// [memory model for page state access]: self#memory-model
    pub(super) unsafe fn from_ptr<'a>(ptr: *mut u64) -> &'a Self {
        // SAFETY: guaranteed by the caller
        let atomic = AtomicU64::from_ptr(ptr);
        // SAFETY: `RawPageState` and `AtomicU64` have the same layout
        mem::transmute(atomic)
    }

    #[inline]
    #[must_use]
    pub(super) fn load(&self) -> PageState {
        self.0.load(Ordering::Relaxed).into()
    }
}

impl RawPageStateMut {
    /// Creates a `RawPageStateMut` from a raw pointer.
    ///
    /// # Safety
    ///
    /// * `ptr` must be properly aligned.
    /// * `ptr` must be [valid] for reads and writes for the whole lifetime `'a`.
    /// * Access to the data pointed by `ptr` must adhere to the [memory model for page state
    ///   access].
    ///
    /// [valid]: core::ptr#safety
    /// [memory model for page state access]: self#memory-model
    pub(super) unsafe fn from_ptr<'a>(ptr: *mut u64) -> &'a Self {
        // SAFETY: guaranteed by the caller
        let atomic = AtomicU64::from_ptr(ptr);
        // SAFETY: `RawPageStateMut` and `AtomicU64` have the same layout
        mem::transmute(atomic)
    }

    #[inline]
    #[must_use]
    #[cfg(test)]
    pub(super) fn load(&self) -> PageState {
        self.0.load(Ordering::Relaxed).into()
    }

    #[inline]
    pub(super) fn store(&self, new: PageState) {
        self.0.store(new.into(), Ordering::Relaxed)
    }

    #[inline]
    pub(super) fn compare_exchange(
        &self,
        current: PageState,
        new: PageState,
    ) -> Result<PageState, PageState> {
        self.0
            .compare_exchange(current.into(), new.into(), Ordering::Relaxed, Ordering::Relaxed)
            .map(PageState::from)
            .map_err(PageState::from)
    }

    #[inline]
    pub(super) fn fetch_update(
        &self,
        mut f: impl FnMut(PageState) -> Option<PageState>,
    ) -> Result<PageState, PageState> {
        self.0
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, move |current| {
                f(current.into()).map(|new| new.into())
            })
            .map(PageState::from)
            .map_err(PageState::from)
    }

    #[inline]
    pub(super) fn unset_dirty(&self) -> PageState {
        self.0.fetch_and(!PageState::DIRTY_MASK, Ordering::Relaxed).into()
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(super) enum PageState {
    Unused,
    Occupied(SnapshotId),
    Dirty(SnapshotId),
}

impl PageState {
    const DIRTY_MASK: u64 = 1 << (u64::BITS - 1);

    #[inline]
    pub(super) fn dirty(snapshot_id: SnapshotId) -> Option<Self> {
        if snapshot_id & Self::DIRTY_MASK != 0 {
            None
        } else {
            Some(Self::Dirty(snapshot_id))
        }
    }

    /// Check if value from a raw pointer is in a dirty state.
    ///
    /// # Safety
    ///
    /// * `ptr` must be properly aligned.
    /// * Access to the data pointed by `ptr` must adhere to the [memory model for page state
    ///   access].
    ///
    /// [valid]: core::ptr#safety
    /// [memory model for page state access]: self#memory-model
    #[inline]
    pub(super) unsafe fn is_dirty(ptr: *mut u64) -> bool {
        // SAFETY: guaranteed by the caller
        *ptr & Self::DIRTY_MASK != 0
    }

    //#[inline]
    //pub(super) fn occupied(snapshot_id: SnapshotId) -> Option<Self> {
    //    if snapshot_id & Self::DIRTY_MASK != 0 {
    //        None
    //    } else {
    //        Some(Self::Occupied(snapshot_id))
    //    }
    //}

    //#[inline]
    //pub(super) fn is_unused(&self) -> bool {
    //    matches!(self, PageState::Unused)
    //}

    //#[inline]
    //pub(super) fn is_occupied(&self) -> bool {
    //    matches!(self, PageState::Occupied(_))
    //}

    //#[inline]
    //pub(super) fn is_dirty(&self) -> bool {
    //    matches!(self, PageState::Dirty(_))
    //}

    #[inline]
    pub(super) fn snapshot_id(&self) -> Option<SnapshotId> {
        match self {
            Self::Unused => None,
            Self::Occupied(snapshot_id) => Some(*snapshot_id),
            Self::Dirty(snapshot_id) => Some(*snapshot_id),
        }
    }
}

impl From<u64> for PageState {
    fn from(value: u64) -> Self {
        let dirty_flag = value & Self::DIRTY_MASK != 0;
        let value = value & !Self::DIRTY_MASK;
        match (dirty_flag, value) {
            (false, 0) => Self::Unused,
            (false, snapshot_id) => Self::Occupied(snapshot_id),
            (true, snapshot_id) => Self::Dirty(snapshot_id),
        }
    }
}

impl From<PageState> for u64 {
    fn from(state: PageState) -> Self {
        match state {
            PageState::Unused => 0,
            PageState::Occupied(snapshot_id) => snapshot_id,
            PageState::Dirty(snapshot_id) => snapshot_id | PageState::DIRTY_MASK,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn state_from_u64() {
        assert_eq!(PageState::from(0), PageState::Unused);
        assert_eq!(PageState::from(0x123), PageState::Occupied(0x123));
        assert_eq!(PageState::from(0x8000000000000123), PageState::Dirty(0x123));
    }

    #[test]
    fn state_is_dirty_from_ptr() {
        let mut data = 123u64;

        let is_dirty = unsafe { PageState::is_dirty(&raw mut data) };
        assert_eq!(is_dirty, false);

        data = data | PageState::DIRTY_MASK;
        let is_dirty = unsafe { PageState::is_dirty(&raw mut data) };
        assert_eq!(is_dirty, true);
    }

    #[test]
    fn raw_page_state_mutations() {
        let mut data = 123u64;

        // Initialize a bunch of `RawPageState` and `RawPageStateMut` objects pointing at the same
        // data.
        let a = unsafe { RawPageState::from_ptr(&raw mut data) };
        let b = unsafe { RawPageState::from_ptr(&raw mut data) };
        let c_mut = unsafe { RawPageStateMut::from_ptr(&raw mut data) };
        let d_mut = unsafe { RawPageStateMut::from_ptr(&raw mut data) };

        // Load the initial data atomically.
        assert_eq!(a.load(), PageState::Occupied(123));
        assert_eq!(b.load(), PageState::Occupied(123));
        assert_eq!(c_mut.load(), PageState::Occupied(123));
        assert_eq!(d_mut.load(), PageState::Occupied(123));

        // Store a new value and check that all objects reflect the new value.
        c_mut.store(PageState::Dirty(456));
        assert_eq!(a.load(), PageState::Dirty(456));
        assert_eq!(b.load(), PageState::Dirty(456));
        assert_eq!(c_mut.load(), PageState::Dirty(456));
        assert_eq!(d_mut.load(), PageState::Dirty(456));

        // Run a `compare_exchange()` that will successfully mutate the value.
        d_mut
            .compare_exchange(PageState::Dirty(456), PageState::Unused)
            .expect("exchange should have succeeded");
        assert_eq!(a.load(), PageState::Unused);
        assert_eq!(b.load(), PageState::Unused);
        assert_eq!(c_mut.load(), PageState::Unused);
        assert_eq!(d_mut.load(), PageState::Unused);

        // Run a `compare_exchange()` that will keep the value unchanged.
        c_mut
            .compare_exchange(PageState::Dirty(456), PageState::Occupied(789))
            .expect_err("exchange should have failed");
        assert_eq!(a.load(), PageState::Unused);
        assert_eq!(b.load(), PageState::Unused);
        assert_eq!(c_mut.load(), PageState::Unused);
        assert_eq!(d_mut.load(), PageState::Unused);

        // Store a dirty value.
        c_mut.store(PageState::Dirty(789));
        assert_eq!(a.load(), PageState::Dirty(789));
        assert_eq!(b.load(), PageState::Dirty(789));
        assert_eq!(c_mut.load(), PageState::Dirty(789));
        assert_eq!(d_mut.load(), PageState::Dirty(789));

        // Unset the dirty flag.
        d_mut.unset_dirty();
        assert_eq!(a.load(), PageState::Occupied(789));
        assert_eq!(b.load(), PageState::Occupied(789));
        assert_eq!(c_mut.load(), PageState::Occupied(789));
        assert_eq!(d_mut.load(), PageState::Occupied(789));

        // Unset the dirty flag again: this will be a no-op.
        d_mut.unset_dirty();
        assert_eq!(a.load(), PageState::Occupied(789));
        assert_eq!(b.load(), PageState::Occupied(789));
        assert_eq!(c_mut.load(), PageState::Occupied(789));
        assert_eq!(d_mut.load(), PageState::Occupied(789));
    }
}
