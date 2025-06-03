use crate::page::PageId;
use proptest_derive::Arbitrary;

/// A concise representation of a node's location in the trie. This is a wrapper around a u32.
/// Values less than 256 are refer to cell ids on the same page, while values 256 and greater refer
/// to the root of another page.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Arbitrary)]
pub struct Location(u32);

impl Location {
    const CELL_MAX: u32 = u8::MAX as u32;
    const PAGE_ID_OFF: u32 = Self::CELL_MAX;

    /// Creates a new [Location] for a page.
    pub fn for_page(page_id: PageId) -> Self {
        Self(Self::PAGE_ID_OFF + page_id.as_u32())
    }

    /// Creates a new [Location] for a cell on the same page.
    pub fn for_cell(cell_index: u8) -> Self {
        Self(cell_index as u32)
    }

    /// Returns the [PageId] of the page if the location is for a page, otherwise returns `None`.
    pub fn page_id(&self) -> Option<PageId> {
        if self.0 <= Self::CELL_MAX {
            None
        } else {
            Some(PageId::new(self.0 - Self::PAGE_ID_OFF).unwrap())
        }
    }

    /// Returns the cell index of the cell if the location is for a cell on the same page, otherwise
    /// returns `None`.
    pub fn cell_index(&self) -> Option<u8> {
        if self.0 >= 256 {
            None
        } else {
            Some(self.0 as u8)
        }
    }
}

impl From<u32> for Location {
    fn from(value: u32) -> Self {
        Self(value)
    }
}

impl From<Location> for u32 {
    fn from(location: Location) -> Self {
        location.0
    }
}

impl From<PageId> for Location {
    fn from(page_id: PageId) -> Self {
        Self::for_page(page_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn test_page_id() {
        for page_id in [PageId::MIN, PageId::MAX] {
            let location = Location::for_page(page_id);
            assert_eq!(location.page_id(), Some(page_id));
            assert_eq!(location.cell_index(), None);
        }
    }

    #[test]
    fn test_cell_index() {
        for cell in 0..=u8::MAX {
            let location = Location::for_cell(cell);
            assert_eq!(location.page_id(), None);
            assert_eq!(location.cell_index(), Some(cell));
        }
    }

    proptest! {
        #[test]
        fn fuzz_location_from_u32(value in any::<u32>()) {
            let location = Location::from(value);
            assert_eq!(location.0, value);
        }

        #[test]
        fn fuzz_location_from_page_id(page_id in any::<PageId>()) {
            let location = Location::for_page(page_id);
            assert_eq!(location.page_id(), Some(page_id));
            assert_eq!(location.cell_index(), None);
        }
    }
}
