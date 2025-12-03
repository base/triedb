//! Database metadata manipulation operations.
//!
//! The database metadata consists of the following elements:
//!
//! * latest [`SnapshotId`] that was committed to the database
//! * [`PageId`] of the root node, and [`B256`] hash of the root node
//! * number of pages in the database
//! * list of orphaned pages in the database
//!
//! # Crash recovery
//!
//! The metadata is backed by a file and aims to be crash-recoverable, meaning that if a crash
//! occurs before or during a commit, the metadata should contain information to restore the
//! database to its previous valid state.
//!
//! The metadata manager achieves this by using a two of strategies, one for the "fixed" metadata
//! (snapshot ID, root node information, number of pages), one for the "variable" metadata (the
//! list of orphaned pages). Both strategies are described below and rely on the assumption that
//! partial writes do not affect the existing data in a file. This assumption may be true at the
//! operating system level, but it's not generally true at the hardware level, thus these
//! strategies will work in case of application crashes, but won't fully protect against kernel
//! panics or power loss events.
//!
//! * The metadata manager maintains two copies of the fixed metadata, which are written in an
//!   alternating fashion: one commit will change the first copy, the next commit will change the
//!   second copy, and so on...
//!
//! * The fixed metadata is hashed so that it's possible to tell whether one of the copies of the
//!   fixed metadata was corrupted by a crash.
//!
//! * The list of orphaned pages is append-only in between commits, and does not get overwritten
//!   until a commit occurs. The following example explains the mechanism:
//!
//!   * Initially, for a new database, the list of orphaned pages will be empty.
//!
//!   * After the first few transactions, it will contain some items:
//!
//!     ```text
//!     page list: [ a b c d e ]
//!                  └───┬───┘
//!                   orphans
//!     ```
//!
//!   * The metadata is then committed and a new transaction comes in. Let's say the transaction
//!     reclaims 2 pages (`a` and `b`) and orphans 2 pages (`f` and `g`). The state will be recorded
//!     as follows:
//!
//!     ```text
//!     page list: [ a b c d e f g ]
//!                  └┬┘ └───┬───┘
//!                   │   orphans
//!                claimed
//!     ```
//!
//!     In words, the first two pages are not wiped from the metadata, but kept and just marked as
//!     "claimed". This way, if a crash occurs, the previous fixed metadata will still report `a b
//!     c d e` as orphans.
//!
//!   * Subsequent transactions will have a similar effect, with new orphans being appended to the
//!     right of the list, and old orphans being reclaimed from the left.
//!
//!   * To prevent the orphan list from growing too big, the list is periodically compactified by
//!     overwriting the claimed section of the list with the actual orphans.

mod error;

use crate::{
    page::{PageId, RawPageId},
    snapshot::SnapshotId,
};
use alloy_primitives::B256;
use memmap2::MmapMut;
use std::{
    cmp::Ordering,
    fs::File,
    io,
    iter::FusedIterator,
    mem,
    ops::{Deref, DerefMut, Not, Range},
    path::Path,
};
use zerocopy::{ByteEq, FromBytes, Immutable, IntoBytes, KnownLayout};

pub use crate::meta::error::{CorruptedMetadataError, OpenMetadataError};

/// Represents the index of one of the metadata slots. Valid values are 0 and 1.
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct SlotIndex(usize);

impl Deref for SlotIndex {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Bit-flips the slot index: converts 0 into 1, and 1 into 0.
impl Not for SlotIndex {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(!*self & 1)
    }
}

/// Fixed-size portion of the metadata slot (excluding the hash).
///
/// This contain the following information:
///
/// * latest snapshot ID;
/// * root node information;
/// * number of allocated pages;
/// * orphan page information.
#[repr(C)]
#[derive(FromBytes, IntoBytes, Immutable, KnownLayout, ByteEq, Clone, Debug)]
pub struct MetadataSlot {
    /// Latest snapshot committed
    snapshot_id: SnapshotId,
    /// Hash of the root node
    root_node_hash: [u8; 32],
    /// Link to the page containing the root node
    root_node_page_id: RawPageId,
    /// Number of pages contained in the data file
    page_count: u32,
    /// Total size of `orphan_pages` (including reclaimed pages)
    orphan_pages_len: u32,
    /// Number of reclaimed pages from the `orphan_pages` list
    reclaimed_orphans_len: u32,
}

impl MetadataSlot {
    /// Returns the latest snapshot committed.
    #[inline]
    #[must_use]
    pub fn snapshot_id(&self) -> SnapshotId {
        self.snapshot_id
    }

    /// Returns the hash of the root node.
    #[inline]
    #[must_use]
    pub fn root_node_hash(&self) -> B256 {
        self.root_node_hash.into()
    }

    /// Returns the ID of the page containing the root node.
    #[inline]
    #[must_use]
    pub fn root_node_page_id(&self) -> Option<PageId> {
        self.root_node_page_id.try_into().ok()
    }

    /// Returns the total number of pages contained in the data file.
    ///
    /// This count includes both used and orphaned pages.
    #[inline]
    #[must_use]
    pub fn page_count(&self) -> u32 {
        self.page_count
    }

    /// Sets the latest snapshot committed.
    #[inline]
    pub fn set_snapshot_id(&mut self, snapshot_id: SnapshotId) {
        self.snapshot_id = snapshot_id;
    }

    /// Increments the snapshot by 1.
    ///
    /// # Panics
    ///
    /// In case of overflow.
    #[inline]
    pub fn inc_snapshot_id(&mut self) {
        self.snapshot_id =
            self.snapshot_id.checked_add(1).expect("integer overflow when increasing snapshot id");
    }

    /// Sets the hash of the root node.
    #[inline]
    pub fn set_root_node_hash(&mut self, root_node_hash: B256) {
        self.root_node_hash = root_node_hash.into();
    }

    /// Sets the ID of the page containing the root node.
    #[inline]
    pub fn set_root_node_page_id(&mut self, root_node_page_id: Option<PageId>) {
        self.root_node_page_id = root_node_page_id.map(RawPageId::from).unwrap_or_default();
    }

    /// Sets the total number of pages contained in the data file.
    ///
    /// This count must include both used and orphaned pages.
    #[inline]
    pub fn set_page_count(&mut self, page_count: u32) {
        self.page_count = page_count;
    }

    /// Returns the range of reclaimed pages in the `orphan_pages` list.
    #[inline]
    #[must_use]
    fn reclaimed_range(&self) -> Range<usize> {
        0..self.reclaimed_orphans_len as usize
    }

    /// Returns the range of pages that are actually orphans (not reclaimed) in the `orphan_pages`
    /// list.
    #[inline]
    #[must_use]
    fn actual_orphans_range(&self) -> Range<usize> {
        debug_assert!(self.orphan_pages_len >= self.reclaimed_orphans_len);
        self.reclaimed_orphans_len as usize..self.orphan_pages_len as usize
    }

    /// Computes the hash for this slot.
    #[inline]
    #[must_use]
    fn hash(&self) -> u64 {
        fxhash::hash64(self.as_bytes())
    }
}

/// Fixed-size portion of the metadata slot (including the hash).
#[repr(C)]
#[derive(FromBytes, IntoBytes, Immutable, KnownLayout, ByteEq, Clone, Debug)]
pub struct HashedMetadataSlot {
    meta: MetadataSlot,
    hash: u64,
}

impl HashedMetadataSlot {
    /// Returns `true` if this metadata slot is uninitialized (its byte representation is all
    /// zeros).
    ///
    /// Uninitialized metadata is considered valid, even though the hash won't compute correctly.
    fn is_empty(&self) -> bool {
        self.as_bytes().iter().copied().all(|byte| byte == 0)
    }

    /// Recomputes the hash for this metadata slots.
    fn update_hash(&mut self) {
        self.hash = self.meta.hash();
    }

    /// Checks if the metadata is not corrupted.
    fn verify_integrity(&self) -> Result<(), CorruptedMetadataError> {
        // Special case: the metadata is uninitialized. In this case, the hash won't match, so quit
        // early.
        if self.is_empty() {
            return Ok(());
        }
        // Check that the number of reclaimed pages doesn't exceed the total number of orphan
        // pages.
        if self.orphan_pages_len < self.reclaimed_orphans_len {
            return Err(CorruptedMetadataError);
        }
        // Check the hash.
        if self.hash != self.meta.hash() {
            return Err(CorruptedMetadataError);
        }
        Ok(())
    }
}

impl Deref for HashedMetadataSlot {
    type Target = MetadataSlot;

    fn deref(&self) -> &Self::Target {
        &self.meta
    }
}

impl DerefMut for HashedMetadataSlot {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.meta
    }
}

impl AsRef<MetadataSlot> for HashedMetadataSlot {
    fn as_ref(&self) -> &MetadataSlot {
        &self.meta
    }
}

impl AsMut<MetadataSlot> for HashedMetadataSlot {
    fn as_mut(&mut self) -> &mut MetadataSlot {
        &mut self.meta
    }
}

#[repr(C)]
#[derive(FromBytes, IntoBytes, Immutable, KnownLayout, ByteEq, Clone, Debug)]
struct MetadataSlots {
    slots: [HashedMetadataSlot; 2],
}

impl MetadataSlots {
    /// Returns the index of the most up-to-date and consistent metadata slot.
    fn latest_slot_index(&self) -> Result<SlotIndex, CorruptedMetadataError> {
        let s0 = &self.slots[0];
        let s1 = &self.slots[1];

        if s0.is_empty() && s1.is_empty() {
            // If both slots are "empty" (zero bytes) it means this metadata is brand new. We can
            // return an arbitrary index
            return Ok(SlotIndex(0));
        }

        // Check if any slot is corrupted. If one of them is corrupted, return the index of the
        // good one
        match (s0.verify_integrity(), s1.verify_integrity()) {
            (Ok(_), Ok(_)) => (),
            (Ok(_), Err(_)) => return Ok(SlotIndex(0)),
            (Err(_), Ok(_)) => return Ok(SlotIndex(1)),
            (Err(_), Err(_)) => return Err(CorruptedMetadataError),
        }

        // If both slots are not corrupted, return the one that has the highest snapshot ID
        match s0.snapshot_id.cmp(&s1.snapshot_id) {
            Ordering::Greater => Ok(SlotIndex(0)),
            Ordering::Less => Ok(SlotIndex(1)),
            Ordering::Equal => {
                // If the snapshot ID is the same, then the two slots must have the same contents
                if s0 == s1 {
                    Ok(SlotIndex(0))
                } else {
                    Err(CorruptedMetadataError)
                }
            }
        }
    }
}

/// Details about an orphan page.
#[repr(C)]
#[derive(FromBytes, IntoBytes, Immutable, KnownLayout, Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct OrphanPage {
    page_id: RawPageId,
    padding: u32,
    orphaned_at: SnapshotId,
}

impl OrphanPage {
    #[inline]
    #[must_use]
    pub fn new(page_id: PageId, orphaned_at: SnapshotId) -> Self {
        Self { page_id: page_id.into(), padding: 0, orphaned_at }
    }

    /// ID of the orphan page.
    #[inline]
    #[must_use]
    pub fn page_id(&self) -> PageId {
        PageId::new(self.page_id).expect("invalid page id in orphan list")
    }

    /// The snapshot at which it was made orphan. Note that this snapshot won't be the same as the
    /// snapshot at which the page was created. This snapshot can be used to understand if there's
    /// any transaction in the system which may still be reading this page.
    #[inline]
    #[must_use]
    pub fn orphaned_at(&self) -> SnapshotId {
        self.orphaned_at
    }
}

#[derive(Debug)]
pub struct MetadataManager {
    file: File,
    mmap: MmapMut,
    active_slot: SlotIndex,
}

impl MetadataManager {
    /// Minimum size for the backing file (4 KiB).
    ///
    /// This is an arbitrary number. The only requirement is for it to be large enough to contain
    /// two `HashedMetadataSlot` structs.
    const SIZE_MIN: u64 = 4096;

    pub fn open(path: impl AsRef<Path>) -> Result<Self, OpenMetadataError> {
        let f = File::options().read(true).write(true).create(true).truncate(false).open(path)?;
        Self::from_file(f)
    }

    pub fn from_file(file: File) -> Result<Self, OpenMetadataError> {
        let initial_file_len = file.metadata()?.len();
        if initial_file_len < Self::SIZE_MIN {
            file.set_len(Self::SIZE_MIN)?;
        }

        let mut mmap = if cfg!(not(miri)) {
            unsafe { MmapMut::map_mut(&file)? }
        } else {
            MmapMut::map_anon(Self::SIZE_MIN as usize)?
        };

        if initial_file_len < Self::SIZE_MIN {
            mmap.as_mut()[initial_file_len as usize..].fill(0);
        }

        let (meta, _) = MetadataSlots::ref_from_prefix(mmap.as_ref())
            .expect("memory map should have the right size and alignment");
        let active_slot = meta.latest_slot_index()?;

        let mut manager = Self { file, mmap, active_slot };
        manager.populate_dirty_slot();
        Ok(manager)
    }

    /// Returns a reference to the active metadata slot.
    ///
    /// This is the slot that was last committed.
    #[inline]
    pub fn active_slot(&self) -> &HashedMetadataSlot {
        let (meta, _) = MetadataSlots::ref_from_prefix(self.mmap.as_ref())
            .expect("memory map should have the right size and alignment");
        &meta.slots[*self.active_slot]
    }

    /// Returns a reference to the dirty metadata slot.
    ///
    /// This is the slot that has not been committed yet.
    #[inline]
    pub fn dirty_slot(&self) -> &HashedMetadataSlot {
        let (meta, _) = MetadataSlots::ref_from_prefix(self.mmap.as_ref())
            .expect("memory map should have the right size and alignment");
        &meta.slots[*!self.active_slot]
    }

    /// Returns a mutable reference to the dirty metadata slot.
    ///
    /// This is the slot that has not been committed yet. Modifications to this slot can be saved
    /// by calling [`commit()`](Self::commit), at which point this slot becomes the active slot.
    #[inline]
    pub fn dirty_slot_mut(&mut self) -> &mut HashedMetadataSlot {
        let (meta, _) = MetadataSlots::mut_from_prefix(self.mmap.as_mut())
            .expect("memory map should have the right size and alignment");
        &mut meta.slots[*!self.active_slot]
    }

    /// Returns a slice containing the orphaned and reclaimed page IDs.
    #[inline]
    fn raw_orphan_pages(&self) -> &[OrphanPage] {
        let (_, remaining_bytes) = MetadataSlots::ref_from_prefix(self.mmap.as_ref())
            .expect("memory map should have the right size and alignment");
        let len = remaining_bytes.len() / mem::size_of::<OrphanPage>();
        <[OrphanPage]>::ref_from_bytes_with_elems(remaining_bytes, len)
            .expect("memory map should have the right size and alignment")
    }

    /// Returns, in this order: an immutable reference to the active slot, a mutable reference to
    /// the dirty slot, a mutable reference to the orphan pages list.
    ///
    /// This convenience method is necessary because Rust borrow rules don't allow obtaining two
    /// mutable references to the same object.
    #[inline]
    fn parts_mut(&mut self) -> (&HashedMetadataSlot, &mut HashedMetadataSlot, &mut [OrphanPage]) {
        let (meta, list) = MetadataSlots::mut_from_prefix(self.mmap.as_mut())
            .expect("memory map should have the right size and alignment");

        let list_len = list.len() / mem::size_of::<OrphanPage>();
        let list = <[OrphanPage]>::mut_from_bytes_with_elems(list, list_len)
            .expect("memory map should have the right size and alignment");

        let [active, dirty] = meta
            .slots
            .get_disjoint_mut([*self.active_slot, *!self.active_slot])
            .expect("memory map should have the right size and alignment");

        (&*active, dirty, list)
    }

    /// Copies the contents of the active slot into the dirty slot, and increases the snapshot ID.
    fn populate_dirty_slot(&mut self) {
        let (active, dirty, _) = self.parts_mut();
        dirty.as_mut_bytes().copy_from_slice(active.as_bytes());
        dirty.inc_snapshot_id();
    }

    /// Changes the size of the memory map.
    ///
    /// # Safety
    ///
    /// `new_len` must be within the size of `self.file`.
    unsafe fn remap(&mut self, new_len: usize) -> io::Result<()> {
        #[cfg(target_os = "linux")]
        {
            unsafe { self.mmap.remap(new_len, memmap2::RemapOptions::new().may_move(true))? };
        }

        #[cfg(not(target_os = "linux"))]
        {
            self.mmap = unsafe { memmap2::MmapOptions::new().len(new_len).map_mut(&self.file)? };
        }

        Ok(())
    }

    /// Doubles the size of the metadata file.
    fn grow(&mut self) -> io::Result<()> {
        let cur_len = mem::size_of::<MetadataSlots>() + mem::size_of_val(self.raw_orphan_pages());
        let new_len = cur_len.saturating_mul(2);
        self.file.set_len(new_len as u64)?;

        unsafe {
            self.remap(new_len)?;
        }

        Ok(())
    }

    fn compact_orphans(&mut self) {
        let (active, dirty, list) = self.parts_mut();
        let reclaimed_range = active.reclaimed_range();
        let actual_orphans_range = dirty.actual_orphans_range();

        // If orphan page list has observed N pushes and M pops, then first of all note that:
        //
        // - N == actual_orphans_range.len()
        // - M == reclaimed_range.len()
        // - N - M = actual_orphans_range.len()
        // - N >= M, or equivalently N - M >= 0
        //
        // Here we move the orphans to the start of the list when M >= N - M, which implies N <=
        // 2M. If that condition is satisfied, we will move N - M items. In total, if the condition
        // is satisfied, we will have performed:
        //
        // - N pushes
        // - M pops
        // - N - M copies
        //
        // for a total of N + M + N - M = 2N operations, which means that adding items to the
        // orphan page list still takes O(1) amortized time.
        if reclaimed_range.len() >= actual_orphans_range.len() {
            dirty.orphan_pages_len = actual_orphans_range.len() as u32;
            dirty.reclaimed_orphans_len = 0;
            list.copy_within(actual_orphans_range, 0);
        }
    }

    /// Saves the metadata to the storage device, and promotes the dirty slot to the active slot.
    ///
    /// After calling this method, a new dirty slot is produced with the same contents as the new
    /// active slot, and an auto-incremented snapshot ID.
    pub fn commit(&mut self) -> io::Result<()> {
        // Compact the orphan page list if there's enough room
        self.compact_orphans();

        // First make sure the changes from the dirty slot are on disk
        self.dirty_slot_mut().update_hash();
        debug_assert!(self.dirty_slot_mut().verify_integrity().is_ok());
        self.sync()?;

        // Then swap the slots, and copy the previously dirty slot (now active) into the previously
        // active slot (now dirty), and increase its snapshot ID
        self.active_slot = !self.active_slot;
        self.populate_dirty_slot();

        Ok(())
    }

    /// Erases the metadata contents.
    pub fn wipe(&mut self) -> io::Result<()> {
        // Set the file length to its initial size
        let size = Self::SIZE_MIN;
        self.file.set_len(size)?;
        unsafe {
            self.remap(size as usize)?;
        }

        // Clear the contents, and re-populate with the initial values
        self.mmap.as_mut()[..size as usize].fill(0);
        self.populate_dirty_slot();

        Ok(())
    }

    /// Saves the metadata to the storage device.
    pub fn sync(&self) -> io::Result<()> {
        if cfg!(not(miri)) {
            self.mmap.flush()
        } else {
            Ok(())
        }
    }

    /// Saves the metadata to the storage device and closes the metadata file.
    pub fn close(self) -> io::Result<()> {
        self.sync()
    }

    /// Returns a mutable object that can be used to inspect and modify the orphan page list.
    #[inline]
    pub fn orphan_pages(&mut self) -> OrphanPages<'_> {
        OrphanPages::new(self)
    }
}

#[must_use]
#[derive(Debug)]
pub struct OrphanPages<'a> {
    manager: &'a mut MetadataManager,
}

impl<'a> OrphanPages<'a> {
    #[inline]
    fn new(manager: &'a mut MetadataManager) -> Self {
        Self { manager }
    }

    /// Number of orphan pages in this list.
    #[inline]
    pub fn len(&self) -> usize {
        let m = self.manager.dirty_slot();
        (m.orphan_pages_len as usize) - (m.reclaimed_orphans_len as usize)
    }

    /// Maximum number of orphan pages that this list can contain without resizing.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.manager.raw_orphan_pages().len()
    }

    /// Returns `true` if there are no orphan pages.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns an iterator that yields the IDs of orphan pages.
    pub fn iter(&self) -> impl FusedIterator<Item = OrphanPage> + use<'_> {
        let list = self.manager.raw_orphan_pages();
        let range = self.manager.dirty_slot().actual_orphans_range();
        list[range].iter().copied()
    }

    /// Adds a page to the orphan page list, increasing the capacity of the list if necessary.
    pub fn push(&mut self, orphan: OrphanPage) -> io::Result<()> {
        if self.push_within_capacity(orphan).is_err() {
            self.manager.grow()?;
            self.push_within_capacity(orphan)
                .expect("`push_within_capacity` failed even though capacity was increased");
        }
        Ok(())
    }

    /// Adds a page to the orphan page list if there is enough capacity.
    pub fn push_within_capacity(&mut self, orphan: OrphanPage) -> Result<(), OrphanPage> {
        let (_, dirty, list) = self.manager.parts_mut();

        let range = dirty.actual_orphans_range();
        if range.end < list.len() {
            if range.end > 0 {
                // In debug mode, ensure that the sequence of orphan page snapshot IDs are
                // non-decreasing. This is because `pop()` makes this assumption, and if this
                // assumption is broken, then the orphan page list may grow indefinetely.
                debug_assert!(orphan.orphaned_at >= list[range.end - 1].orphaned_at);
            }
            list[range.end] = orphan;
            dirty.orphan_pages_len += 1;
            return Ok(());
        }

        // Not enough room to add this orphan.
        Err(orphan)
    }

    /// Reclaims a page from the orphan page list.
    ///
    /// The returned page (if any) is guaranteed to have been orphaned at `snapshot_threshold` or
    /// earlier.
    ///
    /// This method uses an optimized algorithm that may return `None` even if an orphan page
    /// exists.
    pub fn pop(&mut self, snapshot_threshold: SnapshotId) -> Option<OrphanPage> {
        let (_, dirty, list) = self.manager.parts_mut();
        let range = dirty.actual_orphans_range();

        if !range.is_empty() {
            let orphan = list[range.start];
            if orphan.orphaned_at() <= snapshot_threshold {
                dirty.reclaimed_orphans_len += 1;
                return Some(orphan);
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::page::page_id;

    #[test]
    #[cfg_attr(miri, ignore = "persistence is not implemented with miri")]
    fn persistence() {
        let f = tempfile::tempfile().expect("failed to open temporary file");
        let mut manager =
            MetadataManager::from_file(f.try_clone().expect("failed to duplicate file"))
                .expect("failed to initialize metadata manager");
        let dirty = manager.dirty_slot_mut();

        dirty.set_root_node_hash(B256::new([
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
            25, 26, 27, 28, 29, 30, 31, 32,
        ]));
        dirty.set_root_node_page_id(Some(page_id!(123)));
        dirty.set_page_count(456);
        manager.orphan_pages().push(OrphanPage::new(page_id!(0xaa), 1)).expect("push failed");
        manager.orphan_pages().push(OrphanPage::new(page_id!(0xbb), 2)).expect("push failed");
        manager.orphan_pages().push(OrphanPage::new(page_id!(0xcc), 3)).expect("push failed");
        manager.orphan_pages().push(OrphanPage::new(page_id!(0xdd), 4)).expect("push failed");

        manager.commit().expect("commit failed");
        manager.close().expect("close failed");

        let mut manager =
            MetadataManager::from_file(f).expect("failed to initialize metadata manager");

        let active = manager.active_slot();
        assert_eq!(active.snapshot_id(), 1);
        assert_eq!(
            active.root_node_hash(),
            B256::new([
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32
            ])
        );
        assert_eq!(active.root_node_page_id(), Some(page_id!(123)));
        assert_eq!(active.page_count(), 456);
        assert_eq!(
            manager.orphan_pages().iter().collect::<Vec<_>>(),
            [
                OrphanPage::new(page_id!(0xaa), 1),
                OrphanPage::new(page_id!(0xbb), 2),
                OrphanPage::new(page_id!(0xcc), 3),
                OrphanPage::new(page_id!(0xdd), 4),
            ]
        );
    }

    #[test]
    fn auto_increment_snapshot_id() {
        let f = tempfile::tempfile().expect("failed to open temporary file");
        let mut manager =
            MetadataManager::from_file(f.try_clone().expect("failed to duplicate file"))
                .expect("failed to initialize metadata manager");

        for snapshot_id in 0..100 {
            assert_eq!(manager.active_slot().snapshot_id(), snapshot_id);
            assert_eq!(manager.dirty_slot().snapshot_id(), snapshot_id + 1);
            manager.commit().expect("commit failed");
        }
    }

    mod orphan_pages {
        use super::*;
        use std::{
            collections::HashSet,
            io::{Read, Seek, SeekFrom, Write},
        };

        fn push(
            manager: &mut MetadataManager,
            expected: &mut HashSet<OrphanPage>,
            next_page_id: &mut PageId,
        ) {
            let orphan = OrphanPage::new(*next_page_id, 1);
            expected.insert(orphan);
            manager.orphan_pages().push(orphan).expect("push failed");
            *next_page_id = next_page_id.inc().expect("page id overflow");
        }

        fn pop(manager: &mut MetadataManager, expected: &mut HashSet<OrphanPage>) {
            match manager.orphan_pages().pop(1) {
                None => assert!(
                    expected.is_empty(),
                    "metadata manager did not return an orphan page even though {} are available",
                    expected.len()
                ),
                Some(orphan) => assert!(
                    expected.remove(&orphan),
                    "metadata manager returned an orphan page ({orphan:?}) that is not available"
                ),
            }
        }

        fn random_push_pop_cycle(
            manager: &mut MetadataManager,
            expected: &mut HashSet<OrphanPage>,
            next_page_id: &mut PageId,
        ) {
            let iterations = if cfg!(not(miri)) { 100_000 } else { 100 };

            for _ in 0..iterations {
                let push_or_pop = rand::random::<bool>();
                match push_or_pop {
                    true => push(manager, expected, next_page_id),
                    false => pop(manager, expected),
                }

                manager
                    .active_slot()
                    .verify_integrity()
                    .expect("active slot was modified during push/pop operations");
            }
        }

        fn check_orphans(manager: &mut MetadataManager, expected: &HashSet<OrphanPage>) {
            // Use a `Vec`, not a `HashSet`, to check if `orphan_pages()` contains any duplicates
            let mut actual = manager.orphan_pages().iter().collect::<Vec<_>>();
            let mut expected = expected.iter().copied().collect::<Vec<_>>();
            actual.sort_by_key(OrphanPage::page_id);
            expected.sort_by_key(OrphanPage::page_id);
            assert_eq!(expected, actual);
        }

        fn duplicate_file(mut f: &File) -> File {
            let mut dup = tempfile::tempfile().expect("failed to open temporary file");
            f.seek(SeekFrom::Start(0)).expect("seek failed");

            let mut bytes = Vec::new();
            f.read_to_end(&mut bytes).expect("read failed");

            dup.write_all(&bytes).expect("write failed");
            dup
        }

        fn check_orphans_from_file(f: &File, expected: &HashSet<OrphanPage>) {
            let mut manager =
                MetadataManager::from_file(f.try_clone().expect("failed to duplicate file"))
                    .expect("failed to initialize metadata manager");
            check_orphans(&mut manager, expected);
        }

        #[test]
        fn random_push_pop() {
            let f = tempfile::tempfile().expect("failed to open temporary file");
            let mut manager =
                MetadataManager::from_file(f).expect("failed to initialize metadata manager");

            let mut expected = HashSet::new();
            let mut next_page_id = page_id!(1);

            for snapshot_id in 1..=50 {
                random_push_pop_cycle(&mut manager, &mut expected, &mut next_page_id);

                manager.commit().expect("commit failed");
                assert_eq!(manager.active_slot().snapshot_id(), snapshot_id);

                manager
                    .active_slot()
                    .verify_integrity()
                    .expect("active slot should be consistent after a commit");
            }
        }

        #[test]
        fn push_pop() {
            let f = tempfile::tempfile().expect("failed to open temporary file");
            let mut manager =
                MetadataManager::from_file(f).expect("failed to initialize metadata manager");

            // Add 4 pages with increasing snapshots; the orphan page list will look like this:
            // [1, 2, 3, 4]
            manager.orphan_pages().push(OrphanPage::new(page_id!(1), 1)).expect("push failed");
            manager.orphan_pages().push(OrphanPage::new(page_id!(2), 2)).expect("push failed");
            manager.orphan_pages().push(OrphanPage::new(page_id!(3), 3)).expect("push failed");
            manager.orphan_pages().push(OrphanPage::new(page_id!(4), 4)).expect("push failed");
            manager.commit().expect("commit failed");

            // Pop 3 pages; orphan page list: [(claimed), (claimed), (claimed), 4]
            manager.orphan_pages().pop(3).expect("pop failed");
            manager.orphan_pages().pop(3).expect("pop failed");
            manager.orphan_pages().pop(3).expect("pop failed");
            manager.commit().expect("commit failed");

            // Push 2 new pages, again with increasing snapshots; orphan page list: [5, 6,
            // (claimed), 4]
            manager.orphan_pages().push(OrphanPage::new(page_id!(5), 5)).expect("push failed");
            manager.orphan_pages().push(OrphanPage::new(page_id!(6), 6)).expect("push failed");
            manager.commit().expect("commit failed");

            // Pop 2 pages; orphan page list: [(claimed), 6, (claimed), (claimed)]
            manager.orphan_pages().pop(5).expect("pop failed");
            manager.orphan_pages().pop(5).expect("pop failed");
            manager.commit().expect("commit failed");

            assert_eq!(
                manager.orphan_pages().iter().map(|orphan| orphan.page_id).collect::<Vec<_>>(),
                [6]
            );
        }

        #[test]
        #[cfg_attr(miri, ignore = "persistence is not implemented with miri")]
        fn crash_recovery() {
            let f = tempfile::tempfile().expect("failed to open temporary file");
            let mut manager =
                MetadataManager::from_file(f.try_clone().expect("failed to duplicate file"))
                    .expect("failed to initialize metadata manager");

            let mut expected = HashSet::new();
            let mut next_page_id = page_id!(1);

            for snapshot_id in 1..=50 {
                let expected_at_previous_snapshot = expected.clone();

                random_push_pop_cycle(&mut manager, &mut expected, &mut next_page_id);
                manager.sync().expect("sync failed");

                let dup = duplicate_file(&f);
                check_orphans_from_file(&dup, &expected_at_previous_snapshot);

                manager.commit().expect("commit failed");
                assert_eq!(manager.active_slot().snapshot_id(), snapshot_id);
            }
        }
    }
}
