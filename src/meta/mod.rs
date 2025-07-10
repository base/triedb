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
//!   * The metadata is committed again and another transaction comes in. The transaction reclaims 2
//!     pages (`c` and `d`) and orphans 2 pages (`h` and `i`). The state will be recorded as
//!     follows:
//!
//!     ```text
//!     page list: [ h i c d e f g ]
//!                  └┬┘ └┬┘ └─┬─┘
//!                orphans│ orphans
//!                    claimed
//!     ```
//!
//!     In words, the new orphans are written in place of the previously claimed pages. Like
//!     before, if a crash occurs, the previous fixed metadata will still report `c d e f g` as
//!     orphans.
//!
//!   * Let's now supposed a transaction reclaims 2 pages (`e` and `f`) and orphans 5 pages (`j`,
//!     `k`, `l`, `m`, `n`). This will be the new list:
//!
//!     ```text
//!     page list: [ h i j k e f g l m n ]
//!                  └──┬──┘ └┬┘ └──┬──┘
//!                  orphans  │  orphans
//!                        claimed
//!     ```
//!
//!     In words, orphaned pages are added to the previous claimed section until full, and then
//!     appended to the end of the list.
//!
//!   To implement this mechanism, two field are required: the size of the page list, and the range
//!   of claimed pages.

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

macro_rules! mixed_checks_with_else_actions {
    ($out_check:expr, $in_check_1:expr, $in_action_1:expr, $in_check_2:expr, $in_action_2:expr) => {
        if $out_check {
            if $in_check_1 {
                $in_action_1;
            } else if $in_check_2 {
                $in_action_2;
            }
        } else {
            if $in_check_2 {
                $in_action_2;
            } else if $in_check_1 {
                $in_action_1;
            }
        }
    };
}

macro_rules! mixed_checks_actions {
    ($out_check:expr, $in_check_1:expr, $in_action_1:expr, $in_check_2:expr, $in_action_2:expr) => {
        if $out_check {
            if $in_check_1 {
                $in_action_1;
            }
            if $in_check_2 {
                $in_action_2;
            }
        } else {
            if $in_check_2 {
                $in_action_2;
            }
            if $in_check_1 {
                $in_action_1;
            }
        }
    };
}

/// Fixed-size portion of the metadata slot (excluding the hash).
///
/// This contain the following information:
///
/// * latest snapshot ID;
/// * root node information;
/// * number of allocated pages;
/// * orphan page information.
///
/// The orphan page information is used to interpret the contents of the `orphan_pages` list. This
/// list may contain pages that are really orphan and unused, and pages that were orphan in the
/// previous snapshot and were later reclaimed. See the [module-level documentation](self) for more
/// information about why `orphan_pages` contains reclaimed pages.
///
/// The list of reclaimed pages is a contiguous slice inside `orphan_pages` and the meaning of the
/// field in this structure is explained by the following diagram:
///
/// ```text
///               reclaimed pages
///                      ╷
///                   ┌──┴──┐
/// orphan_pages: [ a b c d e f g h ]
///                   │       │     │
///                   │       │     └╴orphan_pages_len
///                   │       └╴reclaimed_orphans_end
///                   └╴reclaimed_orphans_start
/// ```
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
    /// Index of the first reclaimed page inside of `orphan_pages`
    reclaimed_orphans_start: u32,
    /// Number of reclaimed pages inside of `orphan_pages`
    reclaimed_orphans_end: u32,
    /// Unused data to allow this structure to be properly aligned. This padding is stored on disk
    /// to improve runtime performance
    padding: u32,
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
        self.reclaimed_orphans_start as usize..
            (self.reclaimed_orphans_start + self.reclaimed_orphans_end) as usize
    }

    /// Returns the range of pages that are actually orphans (not reclaimed) in the `orphan_pages`
    /// list.
    ///
    /// This returns 2 disjoint ranges because there may be some reclaimed pages in the middle.
    #[inline]
    #[must_use]
    fn actual_orphans_ranges(&self) -> (Range<usize>, Range<usize>) {
        debug_assert!(
            self.orphan_pages_len >= self.reclaimed_orphans_start + self.reclaimed_orphans_end
        );
        (
            0..(self.reclaimed_orphans_start as usize),
            (self.reclaimed_orphans_start as usize + self.reclaimed_orphans_end as usize)..
                (self.orphan_pages_len as usize),
        )
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
        let reclaimed_orphans_end = self
            .reclaimed_orphans_start
            .checked_add(self.reclaimed_orphans_end)
            .ok_or(CorruptedMetadataError)?;
        if self.orphan_pages_len < reclaimed_orphans_end {
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

    /// Doubles the size of the metadata file.
    fn grow(&mut self) -> io::Result<()> {
        let cur_len = mem::size_of::<MetadataSlots>() + mem::size_of_val(self.raw_orphan_pages());
        let new_len = cur_len.saturating_mul(2);
        self.file.set_len(new_len as u64)?;

        #[cfg(target_os = "linux")]
        {
            unsafe { self.mmap.remap(new_len, memmap2::RemapOptions::new().may_move(true))? };
        }
        #[cfg(not(target_os = "linux"))]
        {
            self.mmap = unsafe { MmapMut::map_mut(&self.file)? };
        }

        Ok(())
    }

    /// Saves the metadata to the storage device, and promotes the dirty slot to the active slot.
    ///
    /// After calling this method, a new dirty slot is produced with the same contents as the new
    /// active slot, and an auto-incremented snapshot ID.
    pub fn commit(&mut self) -> io::Result<()> {
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
        let size = Self::SIZE_MIN;
        self.file.set_len(size)?;
        self.mmap.as_mut()[size as usize..].fill(0);
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
        (m.orphan_pages_len as usize) - (m.reclaimed_orphans_end as usize)
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
        let (left, right) = self.manager.dirty_slot().actual_orphans_ranges();
        list[right].iter().copied().chain(list[left].iter().copied())
    }

    /// Adds a page to the orphan page list, increasing the capacity of the list if necessary.
    pub fn push(&mut self, orphan: OrphanPage, snapshot_id: SnapshotId) -> io::Result<()> {
        if self.push_within_capacity(orphan, snapshot_id).is_err() {
            self.manager.grow()?;
            self.push_within_capacity(orphan, snapshot_id)
                .expect("`push_within_capacity` failed even though capacity was increased");
        }
        Ok(())
    }

    /// Adds a page to the orphan page list if there is enough capacity.
    pub fn push_within_capacity(
        &mut self,
        orphan: OrphanPage,
        snapshot_id: SnapshotId,
    ) -> Result<(), OrphanPage> {
        // To make sure the previous snapshot is always valid, we cannot modify orphan pages that
        // are referenced by the previous snapshot. We can only modify the reclaimed orphans
        // slice, or the the additional orphans elements added at the end of the list (if any).
        //
        // Particular care should be taken because a `pop()` may be followed by a `push()`, and
        // it's important that the `push()` does not overwrite data from the previous snapshot.

        let (active, dirty, list) = self.manager.parts_mut();

        // Check if we can write in the reclaimed slice. We can only write in the intersection
        // between the active reclaimed range and the dirty reclaimed range, and only at the bounds
        // of the dirty reclaimed range.
        let active_reclaimed_range = active.reclaimed_range();
        let dirty_reclaimed_range = dirty.reclaimed_range();
        let intersection = active_reclaimed_range.start.max(dirty_reclaimed_range.start)..
            active_reclaimed_range.end.min(dirty_reclaimed_range.end);

        // Push to the beginning or the end of the dirty reclaimed range so that the pop() has a
        // chance to grow up the reclaimed area in another direction.
        //
        // If push() always favours the left side (check start first), the pop() could end up
        // growing the claimed area in area to the right, leaving all the left side orphaned. This
        // could lead to infinite growth of the metadata file as well the data file.
        if !intersection.is_empty() {
            mixed_checks_with_else_actions!(
                snapshot_id & 1 == 0,
                intersection.start == dirty_reclaimed_range.start,
                {
                    list[dirty_reclaimed_range.start] = orphan;
                    dirty.reclaimed_orphans_start += 1;
                    dirty.reclaimed_orphans_end -= 1;
                    return Ok(());
                },
                intersection.end == dirty_reclaimed_range.end,
                {
                    list[dirty_reclaimed_range.end - 1] = orphan;
                    dirty.reclaimed_orphans_end -= 1;
                    return Ok(());
                }
            );
        }

        // We need to write at the end of the list. We can only write past the active and dirty
        // list.
        let (_, active_orphans_range) = active.actual_orphans_ranges();
        let (_, dirty_orphans_range) = dirty.actual_orphans_ranges();
        let index = active_orphans_range.end.max(dirty_orphans_range.end);
        if index < list.len() {
            list[index] = orphan;
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
    pub fn pop(
        &mut self,
        snapshot_threshold: SnapshotId,
        snapshot_id: SnapshotId,
    ) -> Option<OrphanPage> {
        let (_, dirty, list) = self.manager.parts_mut();
        let (left, right) = dirty.actual_orphans_ranges();

        // The following code checks the `left` and `right` ranges for orphaned pages that have an
        // `orphaned_at()` equal or below `snapshot_threshold`.
        //
        // Instead of scanning the whole `left` and `right` lists, the code only check the boundary
        // elements. The assumption is that snapshot IDs are always increasing, never decreasing,
        // and therefore each call to `push()` always adds pages with an increasing
        // `orphaned_at()`. So if the first element has an `orphaned_at()` that is already too
        // high, there's no point in checking the other elements, because they will also be above
        // the threshold.

        // If snapshot_id is even, check the right side first, then the left side. If snapshot_id is
        // odd, check the left side first, then the right side. The priority should be reversed to
        // that of the push() method.
        mixed_checks_actions!(
            snapshot_id & 1 == 0,
            !right.is_empty(),
            {
                let orphan = list[right.start];
                if orphan.orphaned_at() <= snapshot_threshold {
                    dirty.reclaimed_orphans_end += 1;
                    return Some(orphan);
                }
            },
            !left.is_empty(),
            {
                let orphan = list[left.end - 1];
                if orphan.orphaned_at() <= snapshot_threshold {
                    dirty.reclaimed_orphans_start -= 1;
                    dirty.reclaimed_orphans_end += 1;
                    return Some(orphan);
                }
            }
        );

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::page::page_id;

    #[test]
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
        manager.orphan_pages().push(OrphanPage::new(page_id!(0xaa), 1), 2).expect("push failed");
        manager.orphan_pages().push(OrphanPage::new(page_id!(0xbb), 2), 2).expect("push failed");
        manager.orphan_pages().push(OrphanPage::new(page_id!(0xcc), 3), 2).expect("push failed");
        manager.orphan_pages().push(OrphanPage::new(page_id!(0xdd), 4), 2).expect("push failed");

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
            manager.orphan_pages().push(orphan, 2).expect("push failed");
            *next_page_id = next_page_id.inc().expect("page id overflow");
        }

        fn pop(manager: &mut MetadataManager, expected: &mut HashSet<OrphanPage>) {
            match manager.orphan_pages().pop(1, 2) {
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
        fn push_pop() {
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
