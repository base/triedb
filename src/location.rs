#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location(u64);

impl Location {
    pub fn for_page(page_id: u64) -> Self {
        assert!(page_id >= 256);

        Self(page_id)
    }

    pub fn for_cell(cell_index: u8) -> Self {
        Self(cell_index as u64)
    }

    pub fn page_id(&self) -> Option<u64> {
        if self.0 < 256 {
            None
        } else {
            Some(self.0)
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