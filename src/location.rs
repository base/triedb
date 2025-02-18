use crate::page::PageId;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location(u32);

impl Location {
    pub fn for_page(page_id: PageId) -> Self {
        assert!(page_id >= 256);

        Self(page_id)
    }

    pub fn for_cell(cell_index: u8) -> Self {
        Self(cell_index as u32)
    }

    pub fn page_id(&self) -> Option<PageId> {
        if self.0 < 256 {
            None
        } else {
            Some(self.0 as PageId)
        }
    }

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
}
