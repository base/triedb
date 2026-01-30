use crate::{
    page::{
        manager::PageError,
        state::{PageState, RawPageState, RawPageStateMut},
        PageId,
    },
    snapshot::SnapshotId,
};
use std::{fmt, marker::PhantomData, mem, ops::Deref};

// In order to support zero-copy access to the on-disk data, and to ensure the same serialization
// format on all supported platforms, we must stick to one endianness. In practice, this ensures
// that one can copy the database file from one machine to another, and the database software will
// be able to use it reliably.
#[cfg(not(target_endian = "little"))]
compile_error!("This code only supports little-endian platforms");

/// Core structure for both [`Page`] and [`PageMut`].
///
/// This contains the basic information about the page, but does not enforce any particular access
/// pattern.
///
/// This struct mainly exists to allow safe transmutation from [`PageMut`] to [`Page`].
#[derive(Copy, Clone)]
struct UnsafePage {
    id: PageId,
    ptr: *mut [u8; Page::SIZE],
}

#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct Page<'p> {
    inner: UnsafePage,
    phantom: PhantomData<&'p ()>,
}

#[repr(transparent)]
pub struct PageMut<'p> {
    inner: UnsafePage,
    phantom: PhantomData<&'p ()>,
}

fn fmt_page(name: &str, p: &Page<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct(name)
        .field("id", &p.id())
        .field("data", &"[...]")
        .field("snapshot_id", &p.snapshot_id())
        .finish()
}

impl Page<'_> {
    pub const SIZE: usize = 4096;
    pub const HEADER_SIZE: usize = 8;
    pub const DATA_SIZE: usize = Self::SIZE - Self::HEADER_SIZE;

    pub const MAX_COUNT: u32 = PageId::MAX.as_u32() - PageId::MIN.as_u32() + 1;

    /// Constructs a new `Page` from a pointer to an *occupied* page.
    ///
    /// An error is returned if the initial state of the page is found to be unused or dirty.
    ///
    /// # Safety
    ///
    /// * `ptr` must be properly aligned.
    /// * `ptr` must be [valid] for reads for the whole lifetime `'a`.
    /// * Access to the data pointed by `ptr` must adhere to the [memory model for page state
    ///   access].
    ///
    /// [valid]: core::ptr#safety
    /// [memory model for page state access]: state#memory-model
    pub unsafe fn from_ptr(id: PageId, ptr: *mut [u8; Page::SIZE]) -> Result<Self, PageError> {
        // SAFETY: guaranteed by the caller
        match RawPageState::from_ptr(ptr.cast()).load() {
            PageState::Occupied(_) => {
                Ok(Self { inner: UnsafePage { id, ptr }, phantom: PhantomData })
            }
            PageState::Unused => Err(PageError::PageNotFound(id)),
            PageState::Dirty(_) => Err(PageError::PageDirty(id)),
        }
    }

    #[inline]
    pub fn id(&self) -> PageId {
        self.inner.id
    }

    #[inline]
    fn raw_state(&self) -> &RawPageState {
        // SAFETY: `Page` and `RawPageState` have the same safety requirements
        unsafe { RawPageState::from_ptr(self.inner.ptr.cast()) }
    }

    #[inline]
    fn raw_contents(&self) -> &[u8; Page::DATA_SIZE] {
        // SAFETY: `Page::SIZE == Page::HEADER_SIZE + Page::DATA_SIZE` by definition, therefore no
        // overflows will occur.
        unsafe {
            let ptr = self.inner.ptr.byte_add(Page::HEADER_SIZE);
            &*ptr.cast()
        }
    }

    /// Returns the ID of the snapshot at which this page was created.
    #[inline]
    pub fn snapshot_id(&self) -> SnapshotId {
        self.raw_state().load().snapshot_id().unwrap()
    }

    /// Returns the contents of the page without the header
    #[inline]
    pub fn contents(&self) -> &[u8] {
        self.raw_contents()
    }
}

impl fmt::Debug for Page<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_page("Page", self, f)
    }
}

impl<'p> PageMut<'p> {
    /// Constructs a new `PageMut` from a pointer to an *occupied* page.
    ///
    /// The state of the page is atomically transitioned to dirty to ensure exclusive access. An
    /// error is returned if the initial state of the page is found to be dirty.
    ///
    /// # Safety
    ///
    /// * `ptr` must be properly aligned.
    /// * `ptr` must be [valid] for reads and writes for the whole lifetime `'a`.
    /// * Access to the data pointed by `ptr` must adhere to the [memory model for page state
    ///   access].
    /// * `ptr` must not be currently used by any [`Page`] object.
    ///
    /// [valid]: core::ptr#safety
    /// [memory model for page state access]: state#memory-model
    pub unsafe fn from_ptr(
        id: PageId,
        snapshot_id: SnapshotId,
        ptr: *mut [u8; Page::SIZE],
    ) -> Result<Self, PageError> {
        // SAFETY: guaranteed by the caller
        let value: u64 = unsafe { *ptr.cast() };
        match PageState::from(value) {
            PageState::Unused | PageState::Occupied(_) => {
                let mut page = Self { inner: UnsafePage { id, ptr }, phantom: PhantomData };
                page.set_snapshot_id(snapshot_id);
                Ok(page)
            }
            PageState::Dirty(_) => Err(PageError::PageDirty(id)),
        }

        // match RawPageStateMut::from_ptr(ptr.cast()).fetch_update(move |s| match s {
        //     PageState::Unused | PageState::Occupied(_) => Some(new_state),
        //     PageState::Dirty(_) => None,
        // }) {
        //     Ok(_) => Ok(Self { inner: UnsafePage { id, ptr }, phantom: PhantomData }),
        //     Err(PageState::Dirty(_)) => Err(PageError::PageDirty(id)),
        //     Err(PageState::Unused) => unreachable!(),
        //     Err(PageState::Occupied(_)) => unreachable!(),
        // }
    }

    /// Constructs a new `PageMut` from a pointer to an *unused* page.
    ///
    /// The state of the page is atomically transitioned to dirty to ensure exclusive access. An
    /// error is returned if the initial state of the page is found to be occupied or dirty.
    ///
    /// The page contents are initialized to zero.
    ///
    /// # Safety
    ///
    /// * `ptr` must be properly aligned.
    /// * `ptr` must be [valid] for reads and writes for the whole lifetime `'a`.
    /// * Access to the data pointed by `ptr` must adhere to the [memory model for page state
    ///   access].
    /// * `ptr` must not be currently used by any [`Page`] object.
    ///
    /// [valid]: core::ptr#safety
    /// [memory model for page state access]: state#memory-model
    pub unsafe fn acquire(
        id: PageId,
        snapshot_id: SnapshotId,
        ptr: *mut [u8; Page::SIZE],
    ) -> Result<Self, PageError> {
        let new_state = PageState::dirty(snapshot_id).expect("invalid value for `snapshot_id`");

        // SAFETY: guaranteed by the caller
        match RawPageStateMut::from_ptr(ptr.cast()).compare_exchange(PageState::Unused, new_state) {
            Ok(_) => {
                let mut p = Self { inner: UnsafePage { id, ptr }, phantom: PhantomData };
                p.raw_contents_mut().fill(0);
                Ok(p)
            }
            Err(PageState::Occupied(_)) => Err(PageError::PageOccupied(id)),
            Err(PageState::Dirty(_)) => Err(PageError::PageDirty(id)),
            Err(PageState::Unused) => unreachable!(),
        }
    }

    /// Constructs a new `PageMut` from a pointer to an *unused* page, without checking the page
    /// state.
    ///
    /// This method is similar to [`PageMut::acquire`], except for the fact that this method does
    /// not perform any check on the initial state of the page. The purpose of this method is to be
    /// used when operating on uninitialized memory.
    ///
    /// Like for `acquire`, the state of the page is atomically transitioned to dirty to ensure
    /// exclusive access, and the page contents are initialized to zero.
    ///
    /// # Safety
    ///
    /// * `ptr` must be properly aligned.
    /// * `ptr` must be [valid] for reads and writes for the whole lifetime `'a`.
    /// * Access to the data pointed by `ptr` must adhere to the [memory model for page state
    ///   access].
    /// * `ptr` must not be currently used by any [`Page`] or [`PageMut`] object.
    ///
    /// Note that while it's safe to call [`acquire`](PageMut::acquire) multiple times on the same
    /// pointer, calling `acquire_unchecked` multiple times on the same pointer may cause undefined
    /// behavior.
    ///
    /// [valid]: core::ptr#safety
    /// [memory model for page state access]: state#memory-model
    pub unsafe fn acquire_unchecked(
        id: PageId,
        snapshot_id: SnapshotId,
        ptr: *mut [u8; Page::SIZE],
    ) -> Result<Self, PageError> {
        let new_state = PageState::dirty(snapshot_id).expect("invalid value for `snapshot_id`");

        RawPageStateMut::from_ptr(ptr.cast()).store(new_state);
        let mut p = Self { inner: UnsafePage { id, ptr }, phantom: PhantomData };
        p.raw_contents_mut().fill(0);

        Ok(p)
    }

    /// Constructs a new `PageMut` from a mutable reference to an *unused* page.
    ///
    /// This method is safe because the mutable reference ensures that there cannot be any other
    /// living reference to this page.
    pub fn new(id: PageId, snapshot_id: SnapshotId, data: &'p mut [u8; Page::SIZE]) -> Self {
        // SAFETY: `data` is behind a mutable reference, therefore we have exclusive access to the
        // data.
        unsafe { Self::acquire(id, snapshot_id, data) }.unwrap()
    }

    #[inline]
    fn raw_state_mut(&self) -> &RawPageStateMut {
        // SAFETY: `PageMut` and `RawPageState` have the same safety requirements
        unsafe { RawPageStateMut::from_ptr(self.inner.ptr.cast()) }
    }

    #[inline]
    fn raw_contents_mut(&mut self) -> &mut [u8; Page::DATA_SIZE] {
        // SAFETY: `Page::SIZE == Page::HEADER_SIZE + Page::DATA_SIZE` by definition, therefore no
        // overflows will occur.
        unsafe {
            let ptr = self.inner.ptr.byte_add(mem::size_of::<RawPageStateMut>());
            &mut *ptr.cast()
        }
    }

    pub fn set_snapshot_id(&mut self, snapshot_id: SnapshotId) {
        let new_state =
            PageState::dirty(snapshot_id).expect("invalid value for `snapshot_id`: {snapshot_id}");
        self.raw_state_mut().store(new_state);
    }

    /// Returns a mutable reference to the contents of the page without the header
    #[inline]
    pub fn contents_mut(&mut self) -> &mut [u8] {
        self.raw_contents_mut()
    }

    /// Transitions the page state from *dirty* to *occupied*.
    ///
    /// This has the same effect as dropping the page, but it's more explicit.
    pub fn commit(mut self) {
        self.commit_internal();
    }

    /// Transitions the page state from *dirty* to *unused*.
    pub fn discard(self) {
        self.raw_state_mut().store(PageState::Unused);
    }

    /// Transitions the page state from *dirty* to *occupied*, and returns an immutable reference
    /// to the page.
    pub fn downcast(mut self) -> Page<'p> {
        self.commit_internal();
        // SAFETY: `Page` and `PageMut` have the same layout and representation.
        unsafe { mem::transmute(self) }
    }

    fn commit_internal(&mut self) {
        self.raw_state_mut().unset_dirty();
    }
}

impl<'p> Deref for PageMut<'p> {
    type Target = Page<'p>;

    fn deref(&self) -> &Page<'p> {
        // SAFETY: `Page` and `PageMut` have the same layout and representation.
        unsafe { mem::transmute(self) }
    }
}

impl fmt::Debug for PageMut<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_page("PageMut", self, f)
    }
}

impl Drop for PageMut<'_> {
    fn drop(&mut self) {
        self.commit_internal()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::page::page_id;

    #[repr(align(4096))]
    struct DataArray([u8; Page::SIZE]);

    #[test]
    fn test_ref_new() {
        let id = page_id!(42);
        let snapshot = 123u64;
        let mut data = DataArray([0; Page::SIZE]);
        data.0[..8].copy_from_slice(&snapshot.to_le_bytes());

        let page = unsafe { Page::from_ptr(id, &mut data.0).expect("loading page failed") };

        assert_eq!(page.id(), 42);
        assert_eq!(page.snapshot_id(), snapshot);
        assert_eq!(page.contents(), [0u8; Page::DATA_SIZE]);
    }

    #[test]
    fn test_mut_new() {
        let id = page_id!(42);
        let snapshot = 1337;
        let mut data = DataArray([0; Page::SIZE]);

        let page_mut = unsafe {
            PageMut::from_ptr(id, snapshot, &mut data.0).expect("loading mutable page failed")
        };

        assert_eq!(page_mut.id(), 42);
        assert_eq!(page_mut.snapshot_id(), 1337);
        assert_eq!(page_mut.contents(), [0u8; Page::DATA_SIZE]);
    }

    #[test]
    fn test_from_ptr_state_transitions() {
        // Test 1: Unused state
        {
            let id = page_id!(100);
            let snapshot = 500u64;
            let mut data = DataArray([0; Page::SIZE]);
            // Set page state to Unused (all zeros)
            data.0[..8].copy_from_slice(&0u64.to_le_bytes());

            let result = unsafe { PageMut::from_ptr(id, snapshot, &mut data.0) };
            assert!(result.is_ok(), "Expected success on Unused state but got {:?}", result);
            let page_mut = result.unwrap();
            assert_eq!(page_mut.id(), 100);
            assert_eq!(page_mut.snapshot_id(), snapshot);
        }

        // Test 2: Occupied state (should succeed)
        {
            let id = page_id!(101);
            let old_snapshot = 200u64;
            let new_snapshot = 300u64;
            let mut data = DataArray([0; Page::SIZE]);
            // Set page state to Occupied with old_snapshot
            data.0[..8].copy_from_slice(&old_snapshot.to_le_bytes());

            let result = unsafe { PageMut::from_ptr(id, new_snapshot, &mut data.0) };
            assert!(result.is_ok(), "Expected success on Occupied state but got {:?}", result);
            let page_mut = result.unwrap();
            assert_eq!(page_mut.id(), 101);
            assert_eq!(page_mut.snapshot_id(), new_snapshot);
        }

        // Test 3: Dirty state (should fail)
        {
            let id = page_id!(102);
            let old_snapshot = 400u64;
            let new_snapshot = 500u64;
            let mut data = DataArray([0; Page::SIZE]);
            // Set page state to Dirty with old_snapshot (high bit set)
            let dirty_state = old_snapshot | (1u64 << 63);
            data.0[..8].copy_from_slice(&dirty_state.to_le_bytes());

            let result = unsafe { PageMut::from_ptr(id, new_snapshot, &mut data.0) };
            assert!(result.is_err(), "Expected error on Dirty state but got success");
            match result {
                Err(PageError::PageDirty(page_id)) => {
                    assert_eq!(page_id, 102, "Expected page ID 102 in error");
                }
                other => panic!("Expected PageError::PageDirty but got {:?}", other),
            }
        }

        // Test 4: State transition verification
        {
            let id = page_id!(103);
            let snapshot = 600u64;
            let mut data = DataArray([0; Page::SIZE]);
            // Start with Occupied state
            let occupied_snapshot = 700u64;
            data.0[..8].copy_from_slice(&occupied_snapshot.to_le_bytes());

            // Transition to Dirty
            let result = unsafe { PageMut::from_ptr(id, snapshot, &mut data.0) };
            assert!(result.is_ok(), "State transition should succeed");

            // Verify state is now Dirty by checking the raw state
            let state_ptr = data.0.as_mut_ptr() as *mut u64;
            let raw_state = unsafe { state_ptr.read() };
            let expected_dirty = snapshot | (1u64 << 63);
            assert_eq!(raw_state, expected_dirty, "Page state should be Dirty after from_ptr");
        }

        // Test 5: Prevents concurrent access
        {
            let id = page_id!(104);
            let snapshot1 = 800u64;
            let snapshot2 = 900u64;
            let mut data = DataArray([0; Page::SIZE]);
            // Start with Occupied state
            data.0[..8].copy_from_slice(&700u64.to_le_bytes());

            // First call should succeed
            let result1 = unsafe { PageMut::from_ptr(id, snapshot1, &mut data.0) };
            assert!(result1.is_ok(), "First access should succeed");

            // Second call should fail because page is now Dirty
            let result2 = unsafe { PageMut::from_ptr(id, snapshot2, &mut data.0) };
            assert!(result2.is_err(), "Second access should fail");
            assert!(
                matches!(result2, Err(PageError::PageDirty(_))),
                "Expected PageDirty error but got {:?}",
                result2
            );
        }
    }
}
