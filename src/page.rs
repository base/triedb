use proptest_derive::Arbitrary;
use std::{
    cmp, fmt,
    num::{NonZero, ParseIntError, TryFromIntError},
    str::FromStr,
};
use zerocopy::{Immutable, IntoBytes, KnownLayout};

mod manager;
mod page;
mod slotted_page;
mod state;

pub use manager::{mmap::PageManager, options::PageManagerOptions, PageError};
pub use page::{Page, PageMut};
pub use slotted_page::{SlottedPage, SlottedPageMut, CELL_POINTER_SIZE};

/// Primitive type for [`PageId`].
///
/// This is an integer type large enough to contain all valid values for [`PageId`]. Every `PageId`
/// can be converted to a `RawPageId`, but not all `RawPageId`s are valid `PageId`s.
///
/// `PageId` can be converted to/from `RawPageId` using [`PageId::new()`] and [`PageId::as_u32()`].
pub type RawPageId = u32;

/// Type representing an ID for [`Page`] objects.
///
/// IDs range from 1 to `u32::MAX - 255` (inclusive). The reasons for the bounds are the following:
///
/// * the value 0 is used in several places as a special value to signify a null pointer;
/// * [`triedb::Location`] reserves a special role for integers in the range from 0 to 255
///   (inclusive), and `PageId` values inside `Location` are represented by adding 255 to them.
///
/// `PageId` offers the following memory layout optimization: `Option<PageId>` has the same size as
/// `PageId`, which in turn has the same size as `u32`.
#[repr(transparent)]
#[derive(
    IntoBytes,
    Immutable,
    KnownLayout,
    Copy,
    Clone,
    Arbitrary,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Debug,
)]
pub struct PageId(NonZero<u32>);

// Verify the memory layout optimization of `PageId`, that is: `PageId`, `Option<PageId>`, and
// `u32` all have the same size.
static_assertions::assert_eq_size!(PageId, Option<PageId>, u32);

impl PageId {
    /// Minimum valid value for a `PageId`.
    pub const MIN: Self = Self(NonZero::new(1).unwrap());
    /// Maximum valid value for a `PageId`.
    pub const MAX: Self = Self(NonZero::new(u32::MAX - 255).unwrap());

    #[inline]
    #[must_use]
    const fn is_valid(id: u32) -> bool {
        id >= Self::MIN.as_u32() && id <= Self::MAX.as_u32()
    }

    /// Constructs a new `PageId` from an `u32`.
    #[inline]
    #[must_use]
    pub const fn new(id: u32) -> Option<Self> {
        if Self::is_valid(id) {
            Some(unsafe { Self::new_unchecked(id) })
        } else {
            None
        }
    }

    /// Constructs a new `PageId` from an `u32` without performing any check.
    ///
    /// # Safety
    ///
    /// `id` must be between [`PageId::MIN`]` and [`PageId::MAX`] (inclusive).
    #[inline]
    #[must_use]
    pub const unsafe fn new_unchecked(id: u32) -> Self {
        debug_assert!(
            Self::is_valid(id),
            "PageId::new_unchecked requires the argument to be between PageId::MIN and PageId::MAX"
        );
        Self(NonZero::new_unchecked(id))
    }

    /// Returns the page ID as an `u32`.
    #[inline]
    #[must_use]
    pub const fn as_u32(&self) -> u32 {
        self.0.get()
    }

    /// Returns the page ID as an `usize`.
    #[inline]
    #[must_use]
    pub const fn as_usize(&self) -> usize {
        self.as_u32() as usize
    }

    /// Returns the byte offset where the page would be located inside a page file.
    #[inline]
    #[must_use]
    pub const fn as_offset(&self) -> usize {
        (self.as_usize() - 1) * Page::SIZE
    }

    /// Increments the `PageId` by 1.
    ///
    /// Returns `None` in case the operation would overflow (exceeding [`PageId::MAX`]).
    #[inline]
    #[must_use]
    pub fn inc(&self) -> Option<Self> {
        self.as_u32().checked_add(1).and_then(Self::new)
    }
}

impl TryFrom<u32> for PageId {
    type Error = TryFromIntError;

    #[inline]
    fn try_from(id: u32) -> Result<Self, Self::Error> {
        Self::new(id).ok_or_else(|| {
            // It's not possible to directly construct a `TryFromIntError`, so we just steal it
            // from another function.
            NonZero::try_from(0).unwrap_err()
        })
    }
}

impl From<PageId> for u32 {
    fn from(id: PageId) -> Self {
        id.0.get()
    }
}

impl From<PageId> for NonZero<u32> {
    fn from(id: PageId) -> Self {
        id.0
    }
}

impl PartialEq<u32> for PageId {
    #[inline]
    fn eq(&self, other: &u32) -> bool {
        self.0.get().eq(other)
    }
}

impl PartialOrd<u32> for PageId {
    #[inline]
    fn partial_cmp(&self, other: &u32) -> Option<cmp::Ordering> {
        self.0.get().partial_cmp(other)
    }
}

impl PartialEq<PageId> for u32 {
    #[inline]
    fn eq(&self, other: &PageId) -> bool {
        self.eq(&other.0.get())
    }
}

impl PartialOrd<PageId> for u32 {
    #[inline]
    fn partial_cmp(&self, other: &PageId) -> Option<cmp::Ordering> {
        self.partial_cmp(&other.0.get())
    }
}

impl fmt::Display for PageId {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.get().fmt(f)
    }
}

impl FromStr for PageId {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let value = NonZero::<u32>::from_str(s)?.get();
        Self::new(value).ok_or_else(|| {
            // Like for `TryFromIntError`, it is not possible to construct a `ParseIntError`, so we
            // just steal the error by trying to create an `u32` from a string that is too large to
            // be represented as an `u32`.
            u32::from_str("5000000000").unwrap_err()
        })
    }
}

/// Helper macro to construct [`PageId`] from a `const` expression.
///
/// This macro checks at compile time that the given ID is valid and returns a `PageId` object
/// (unlike `PageId::new()`, which returns an `Option<PageId>`, and unlike
/// `PageId::new_unchecked()`, which is `unsafe`).
///
/// This macro is mainly useful for tests, where page IDs are often hardcoded integers.
///
/// # Example
///
/// ```
/// use triedb::page::{page_id, PageId};
///
/// let id = page_id!(123);
/// assert_eq!(id, PageId::new(123).unwrap());
/// ```
#[macro_export]
macro_rules! page_id {
    ( $id:expr ) => {{
        const MAYBE_ID: Option<$crate::page::PageId> = $crate::page::PageId::new($id);
        ::static_assertions::const_assert!(MAYBE_ID.is_some());
        MAYBE_ID.expect("id was checked for validity at compile-time")
    }};
}

pub use page_id;
