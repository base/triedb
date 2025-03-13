use crate::page::PageId;
use proptest_derive::Arbitrary;

/// A concise representation of a node's location in the trie. This is a wrapper around a u32.
/// Values less than 256 are refer to cell ids on the same page, while values 256 and greater refer
/// to the root of another page.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Arbitrary)]
pub struct Location(u32);

impl Location {
    /// Creates a new [Location] for a page.
    ///
    /// # Panics
    ///
    /// This function will panic if the provided [PageId] is less than 256.
    pub fn for_page(page_id: PageId) -> Self {
        assert!(page_id >= 256);

        Self(page_id)
    }

    /// Creates a new [Location] for a cell on the same page.
    pub fn for_cell(cell_index: u8) -> Self {
        Self(cell_index as u32)
    }

    /// Returns the [PageId] of the page if the location is for a page, otherwise returns `None`.
    pub fn page_id(&self) -> Option<PageId> {
        if self.0 < 256 {
            None
        } else {
            Some(self.0 as PageId)
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

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn test_page_id() {
        let location = Location::for_page(1000);
        assert_eq!(location.page_id(), Some(1000));
        assert_eq!(location.cell_index(), None);
    }

    #[test]
    #[should_panic]
    fn test_page_id_panic() {
        Location::for_page(255);
    }

    #[test]
    fn test_cell_index() {
        let location = Location::for_cell(100);
        assert_eq!(location.page_id(), None);
        assert_eq!(location.cell_index(), Some(100));
    }

    proptest! {
        #[test]
        fn fuzz_location_from_u32(value in any::<u32>()) {
            let location = Location::from(value);
            assert_eq!(location.0, value);
        }
    }
}
