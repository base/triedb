use crate::page::{PageError, PAGE_DATA_SIZE};

// A pointer to a page cell, which encodes the offset and length as 12-bit numbers in 3 bytes.
pub(crate) struct CellPointer<'p>(&'p [u8; 3]);

#[derive(Debug)]
pub enum CellPointerError {
    InvalidLength,
}

impl From<CellPointerError> for PageError {
    fn from(error: CellPointerError) -> Self {
        match error {
            CellPointerError::InvalidLength => PageError::InvalidCellPointer,
        }
    }
}

impl<'p> CellPointer<'p> {
    // Creates a new cell pointer and writes it to the given data.
    pub fn new(offset: u16, length: u16, data: &'p mut [u8; 3]) -> Self {
        assert!(offset < PAGE_DATA_SIZE as u16);
        assert!(length < PAGE_DATA_SIZE as u16);
        assert!(offset >= length);

        data[0] = (offset >> 4) as u8;
        data[1] = ((offset as u8 & 0b1111) << 4) | (length >> 8) as u8;
        data[2] = length as u8;
        Self(data)
    }

    // Returns the offset of the cell pointer (0-4095), derived from the first 12 bits.
    pub fn offset(&self) -> u16 {
        ((self.0[0] as u16) << 4) | (self.0[1] >> 4) as u16
    }

    // Returns the length of the cell pointer, derived from the last 12 bits.
    pub fn length(&self) -> u16 {
        ((self.0[1] as u16 & 0b1111) << 8) | self.0[2] as u16
    }

    // Returns true if the cell pointer is deleted (all bytes are 0).
    pub fn is_deleted(&self) -> bool {
        (self.0[0] | self.0[1] | self.0[2]) == 0
    }
}

impl std::fmt::Debug for CellPointer<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CellPointer {{ offset: {}, length: {} }}", self.offset(), self.length())
    }
}

impl<'p> From<CellPointer<'p>> for &'p [u8; 3] {
    fn from(cell_pointer: CellPointer<'p>) -> Self {
        cell_pointer.0
    }
}

impl<'p> TryFrom<&'p [u8]> for CellPointer<'p> {
    type Error = CellPointerError;

    fn try_from(data: &'p [u8]) -> Result<Self, Self::Error> {
        if data.len() != 3 {
            return Err(CellPointerError::InvalidLength);
        }
        Ok(CellPointer(data.try_into().unwrap()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cell_pointer() {
        let cell_pointer = CellPointer(&[0b00000000, 0b00000000, 0b00000000]);
        assert_eq!(cell_pointer.offset(), 0);
        assert_eq!(cell_pointer.length(), 0);
        assert!(cell_pointer.is_deleted());

        let cell_pointer = CellPointer(&[0b11111111, 0b11111111, 0b11111111]);
        assert_eq!(cell_pointer.offset(), 4095);
        assert_eq!(cell_pointer.length(), 4095);
        assert!(!cell_pointer.is_deleted());

        let cell_pointer = CellPointer(&[0b11111111, 0b11110000, 0b00000000]);
        assert_eq!(cell_pointer.offset(), 4095);
        assert_eq!(cell_pointer.length(), 0);
        assert!(!cell_pointer.is_deleted());

        let cell_pointer = CellPointer(&[0b00000000, 0b00001111, 0b11111111]);
        assert_eq!(cell_pointer.offset(), 0);
        assert_eq!(cell_pointer.length(), 4095);
        assert!(!cell_pointer.is_deleted());

        let mut data = [0; 3];
        let cell_pointer = CellPointer::new(1234, 567, &mut data);
        assert_eq!(cell_pointer.offset(), 1234);
        assert_eq!(cell_pointer.length(), 567);
        assert!(!cell_pointer.is_deleted());
        assert_eq!(data, [0b01001101, 0b00100010, 0b00110111]);

        let cell_pointer = CellPointer::new(0, 0, &mut data);
        assert_eq!(cell_pointer.offset(), 0);
        assert_eq!(cell_pointer.length(), 0);
        assert!(cell_pointer.is_deleted());
    }
}
