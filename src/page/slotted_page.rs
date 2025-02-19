use core::slice;
use std::cmp::max;
use std::fmt::Debug;

use super::{
    page::{PageKind, RO, RW},
    Page, PageError, PAGE_DATA_SIZE,
};

pub mod cell_pointer;
use cell_pointer::CellPointer;

const MAX_NUM_CELLS: u8 = 255; // With 1 byte for the number of cells, the maximum number of cells is 255.

pub trait Value<'v>: TryFrom<&'v [u8]> + TryInto<&'v [u8], Error: Debug> + Debug {}

impl<'v> Value<'v> for &'v [u8] {}

pub trait SlottedStorage<'s, 'v, V> {
    type Error;

    // Returns the value at the given index.
    fn get_value(&'v self, index: u8) -> Result<V, Self::Error>
    where
        's: 'v;
}

// A page that contains a sequence of pointers to variable-length values,
// where the pointers are stored in a contiguous array of 3-byte cell pointers from the
// beginning of the page, and the values are added from the end of the page.
pub struct SlottedPage<'p, P: PageKind> {
    page: Page<'p, P>,
}

impl<'p, P: PageKind> SlottedPage<'p, P> {
    // Returns the value at the given index.
    pub fn get_value<'v, V: Value<'v>>(&self, index: u8) -> Result<V, PageError>
    where
        'p: 'v,
    {
        let cell_pointer = self.get_cell_pointer(index)?;
        if cell_pointer.is_deleted() {
            return Err(PageError::InvalidCellPointer);
        }

        let offset = cell_pointer.offset();
        let length = cell_pointer.length();

        let start_index = (PAGE_DATA_SIZE as u16 - offset) as usize;

        let data = unsafe {
            slice::from_raw_parts(
                self.page.contents().as_ptr().add(start_index),
                length as usize,
            )
        };
        data.try_into().map_err(|_| PageError::InvalidCellPointer)
    }

    // Returns the cell pointer at the given index.
    fn get_cell_pointer(&self, index: u8) -> Result<CellPointer, PageError> {
        if index >= self.num_cells() {
            return Err(PageError::InvalidCellPointer);
        }
        let start_index = 1 + 3 * (index as usize);
        let end_index = start_index + 3;
        let data = &self.page.contents()[start_index..end_index];
        Ok(data.try_into()?)
    }

    // Returns the number of cells in the page, which may include deleted cells.
    fn num_cells(&self) -> u8 {
        self.page.contents()[0]
    }
}

impl<'p, 'v, P: PageKind, V: Value<'v>> SlottedStorage<'p, 'v, V> for SlottedPage<'p, P> {
    type Error = PageError;

    fn get_value(&'v self, index: u8) -> Result<V, Self::Error>
    where
        'p: 'v,
    {
        self.get_value(index)
    }
}

impl<'p> SlottedPage<'p, RW> {
    // Sets the value at the given index.
    pub fn set_value<'v, V: Value<'v>>(&mut self, index: u8, value: V) -> Result<(), PageError>
    where
        'p: 'v,
    {
        let cell_pointer = self.get_cell_pointer(index)?;

        let offset = cell_pointer.offset();
        let length = cell_pointer.length();
        let start_index = (PAGE_DATA_SIZE as u16 - offset) as usize;
        let end_index = (PAGE_DATA_SIZE as u16 - offset + length) as usize;
        let data = &mut self.page.contents_mut()[start_index..end_index];
        data.copy_from_slice(value.try_into().unwrap());
        Ok(())
    }

    // Inserts a value into the page and returns the index of the new value.
    pub fn insert_value<'v, V: Value<'v>>(&mut self, value: V) -> Result<u8, PageError>
    where
        'p: 'v,
    {
        let cell_index = self.next_free_cell_index()?;
        let value_data = value.try_into().unwrap();
        let cell_pointer = self.allocate_cell_pointer(cell_index, value_data.len() as u16)?;

        let offset = cell_pointer.offset();
        let length = cell_pointer.length();
        let start_index = (PAGE_DATA_SIZE as u16 - offset) as usize;
        let end_index = (PAGE_DATA_SIZE as u16 - offset + length) as usize;
        let data = &mut self.page.contents_mut()[start_index..end_index];
        data.copy_from_slice(value_data);
        Ok(cell_index)
    }

    // Deletes the value at the given index.
    pub fn delete_value(&mut self, index: u8) -> Result<(), PageError> {
        let num_cells = self.num_cells();
        self.set_cell_pointer(index, 0, 0)?;
        let mut new_num_cells = num_cells;
        // iterate over the cells in reverse order, decrementing the number of cells
        for i in (0..num_cells).rev() {
            if !self.get_cell_pointer(i)?.is_deleted() {
                break;
            }
            new_num_cells -= 1;
        }
        if new_num_cells < num_cells {
            self.set_num_cells(new_num_cells);
        }
        Ok(())
    }

    // Returns the index of the next free cell in the page, which may include deleted cells.
    fn next_free_cell_index(&self) -> Result<u8, PageError> {
        let num_cells = self.num_cells();
        for i in 0..num_cells {
            if self.get_cell_pointer(i)?.is_deleted() {
                return Ok(i);
            }
        }
        if num_cells == MAX_NUM_CELLS {
            return Err(PageError::NoFreeCells);
        }
        Ok(num_cells)
    }

    // Allocates a cell pointer at the given index with the given length and returns the cell pointer.
    fn allocate_cell_pointer(&mut self, index: u8, length: u16) -> Result<CellPointer, PageError> {
        match self.find_available_slot(index, length)? {
            Some(offset) => {
                let num_cells = self.num_cells();
                let new_num_cells = max(num_cells, index + 1);

                if new_num_cells > num_cells {
                    self.set_num_cells(new_num_cells);
                }
                return self.set_cell_pointer(index, offset, length);
            }
            None => {
                // TODO: defragment the page
                Err(PageError::PageIsFull)
            }
        }
    }

    // Finds a free space with length in the page. Returns slotted page offset if found.
    fn find_available_slot(&self, index: u8, length: u16) -> Result<Option<u16>, PageError> {
        match self.find_available_slot_in_used_space(length)? {
            Some(offset) => Ok(Some(offset)),
            None => self.find_available_slot_in_remaining_space(index, length),
        }
    }

    fn find_available_slot_in_used_space(&self, length: u16) -> Result<Option<u16>, PageError> {
        let num_cells = self.num_cells();
        let mut used_space = (0..num_cells).try_fold(
            Vec::new(),
            |mut acc, i| -> Result<Vec<(u16, u16)>, PageError> {
                let cp = self.get_cell_pointer(i)?;
                if !cp.is_deleted() {
                    acc.push((cp.offset() - cp.length(), cp.offset()));
                }
                Ok(acc)
            },
        )?;
        used_space.sort_by(|a, b| a.1.cmp(&b.1));

        if used_space.len() > 1 {
            for i in 0..used_space.len() - 1 {
                if used_space[i + 1].0 - used_space[i].1 >= length {
                    return Ok(Some(used_space[i].1 + length));
                }
            }
        }
        Ok(None)
    }

    fn find_available_slot_in_remaining_space(
        &self,
        index: u8,
        length: u16,
    ) -> Result<Option<u16>, PageError> {
        let num_cells = self.num_cells();
        let new_num_cells = max(num_cells, index + 1);
        let mut max_offset = 0;
        for i in 0..num_cells {
            let offset = self.get_cell_pointer(i)?.offset();
            if offset > max_offset {
                max_offset = offset;
            }
        }

        let offset = max_offset + length;

        if offset as usize > self.page.contents().len() - new_num_cells as usize * 3 - 1 {
            return Ok(None);
        }

        Ok(Some(offset))
    }

    // Sets the cell pointer at the given index.
    fn set_cell_pointer(
        &mut self,
        index: u8,
        offset: u16,
        length: u16,
    ) -> Result<CellPointer, PageError> {
        let start_index = 1 + 3 * (index as usize);
        let end_index = start_index + 3;
        let data = &mut self.page.contents_mut()[start_index..end_index];
        let cell_pointer = CellPointer::new(offset, length, data.try_into().unwrap());
        Ok(cell_pointer)
    }

    // Sets the number of cells in the page.
    fn set_num_cells(&mut self, num_cells: u8) {
        self.page.contents_mut()[0] = num_cells;
    }
}

impl<'p, P: PageKind> From<SlottedPage<'p, P>> for Page<'p, P> {
    fn from(page: SlottedPage<'p, P>) -> Self {
        page.page
    }
}

impl<'p> From<SlottedPage<'p, RW>> for SlottedPage<'p, RO> {
    fn from(page: SlottedPage<'p, RW>) -> Self {
        Self {
            page: page.page.into(),
        }
    }
}

impl<'p, P: PageKind> TryFrom<Page<'p, P>> for SlottedPage<'p, P> {
    type Error = PageError;

    fn try_from(page: Page<'p, P>) -> Result<Self, Self::Error> {
        Ok(Self { page })
    }
}

#[cfg(test)]
mod tests {
    use crate::page::PAGE_SIZE;

    use super::*;

    #[test]
    fn test_insert_get_value() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();

        let v1: &[u8] = &[1, 2, 3];
        let i1 = subtrie_page.insert_value(v1).unwrap();
        assert_eq!(i1, 0);

        let v: &[u8] = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        let v2: &[u8] = &[4, 5, 6];
        let i2 = subtrie_page.insert_value(v2).unwrap();
        assert_eq!(i2, 1);

        let v: &[u8] = subtrie_page.get_value(i2).unwrap();
        assert_eq!(v, v2);

        // ensure the first cell is not modified
        let v: &[u8] = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        // sanity check the page
        assert_eq!(subtrie_page.num_cells(), 2);
    }

    #[test]
    fn test_insert_set_value() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();

        let v1: &[u8] = &[1, 2, 3];
        let i1 = subtrie_page.insert_value(v1).unwrap();
        assert_eq!(i1, 0);

        let v: &[u8] = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        let v2: &[u8] = &[4, 5, 6];
        subtrie_page.set_value(i1, v2).unwrap();

        let v: &[u8] = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v2);
    }

    #[test]
    fn test_allocate_get_delete_cell_pointer() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();
        let cell_index = subtrie_page.insert_value(&[1, 2, 3][..]).unwrap();
        assert_eq!(cell_index, 0);
        assert_eq!(subtrie_page.num_cells(), 1);
        assert_eq!(subtrie_page.get_cell_pointer(0).unwrap().length(), 3);
        assert_eq!(subtrie_page.get_cell_pointer(0).unwrap().offset(), 3);

        let cell_index = subtrie_page.insert_value(&[4, 5, 6][..]).unwrap();
        assert_eq!(cell_index, 1);
        assert_eq!(subtrie_page.num_cells(), 2);
        assert_eq!(subtrie_page.get_cell_pointer(1).unwrap().length(), 3);
        assert_eq!(subtrie_page.get_cell_pointer(1).unwrap().offset(), 6);

        let cell_index = subtrie_page.insert_value(&[88; 88][..]).unwrap();
        assert_eq!(cell_index, 2);
        assert_eq!(subtrie_page.num_cells(), 3);
        assert_eq!(subtrie_page.get_cell_pointer(2).unwrap().length(), 88);
        assert_eq!(subtrie_page.get_cell_pointer(2).unwrap().offset(), 94);

        let cell_index = subtrie_page.insert_value(&[88; 88][..]).unwrap();
        assert_eq!(cell_index, 3);
        assert_eq!(subtrie_page.num_cells(), 4);
        assert_eq!(subtrie_page.get_cell_pointer(3).unwrap().length(), 88);
        assert_eq!(subtrie_page.get_cell_pointer(3).unwrap().offset(), 182);

        let cell_index = subtrie_page.insert_value(&[88; 88][..]).unwrap();
        assert_eq!(cell_index, 4);
        assert_eq!(subtrie_page.num_cells(), 5);
        assert_eq!(subtrie_page.get_cell_pointer(4).unwrap().length(), 88);
        assert_eq!(subtrie_page.get_cell_pointer(4).unwrap().offset(), 270);

        // remaining space should be 4088 - 1 - 3*5 - 270 = 3892
        // still need enough space for the new cell pointer (3 bytes), so this should fail
        let cell_index = subtrie_page.insert_value(&[255; 3802][..]);
        assert!(cell_index.is_err());
        assert!(matches!(cell_index, Err(PageError::PageIsFull)));
        assert_eq!(subtrie_page.num_cells(), 5);

        let cell_index = subtrie_page.insert_value(&[255; 3801][..]);
        assert!(cell_index.is_err());
        assert!(matches!(cell_index, Err(PageError::PageIsFull)));
        assert_eq!(subtrie_page.num_cells(), 5);

        let cell_index = subtrie_page.insert_value(&[255; 3800][..]);
        assert!(cell_index.is_err());
        assert!(matches!(cell_index, Err(PageError::PageIsFull)));
        assert_eq!(subtrie_page.num_cells(), 5);

        let cell_index = subtrie_page.insert_value(&[255; 3799][..]).unwrap();
        assert_eq!(cell_index, 5);
        assert_eq!(subtrie_page.num_cells(), 6);
        assert_eq!(subtrie_page.get_cell_pointer(5).unwrap().length(), 3799);
        assert_eq!(subtrie_page.get_cell_pointer(5).unwrap().offset(), 4069);

        subtrie_page.delete_value(0).unwrap();
        assert_eq!(subtrie_page.num_cells(), 6);
        assert_eq!(subtrie_page.get_cell_pointer(0).unwrap().length(), 0);
        assert_eq!(subtrie_page.get_cell_pointer(0).unwrap().offset(), 0);

        subtrie_page.delete_value(5).unwrap();
        assert_eq!(subtrie_page.num_cells(), 5);
        assert!(matches!(
            subtrie_page.get_cell_pointer(5),
            Err(PageError::InvalidCellPointer)
        ));

        subtrie_page.delete_value(4).unwrap();
        assert_eq!(subtrie_page.num_cells(), 4);
        assert!(matches!(
            subtrie_page.get_cell_pointer(4),
            Err(PageError::InvalidCellPointer)
        ));

        subtrie_page.delete_value(3).unwrap();
        assert_eq!(subtrie_page.num_cells(), 3);
        assert!(matches!(
            subtrie_page.get_cell_pointer(3),
            Err(PageError::InvalidCellPointer)
        ));

        subtrie_page.delete_value(2).unwrap();
        assert_eq!(subtrie_page.num_cells(), 2);
        assert!(matches!(
            subtrie_page.get_cell_pointer(2),
            Err(PageError::InvalidCellPointer)
        ));

        subtrie_page.delete_value(1).unwrap();
        assert_eq!(subtrie_page.num_cells(), 0);
        assert!(matches!(
            subtrie_page.get_cell_pointer(1),
            Err(PageError::InvalidCellPointer)
        ));
        assert!(matches!(
            subtrie_page.get_cell_pointer(0),
            Err(PageError::InvalidCellPointer)
        ));

        // after cleaning up all of the cells, we should be able to allocate a maximum sized cell
        // 4088 - 1 - 3 = 4084
        let cell_index = subtrie_page.insert_value(&[255; 4084][..]).unwrap();
        assert_eq!(cell_index, 0);
        assert_eq!(subtrie_page.num_cells(), 1);
        assert_eq!(subtrie_page.get_cell_pointer(0).unwrap().length(), 4084);
        assert_eq!(subtrie_page.get_cell_pointer(0).unwrap().offset(), 4084);
    }

    #[test]
    fn test_allocate_reuse_deleted_space() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();

        let i0 = subtrie_page.insert_value(&[11; 1020][..]).unwrap();
        assert_eq!(i0, 0);

        let i1 = subtrie_page.insert_value(&[11; 1020][..]).unwrap();
        assert_eq!(i1, 1);

        let i2 = subtrie_page.insert_value(&[11; 1020][..]).unwrap();
        assert_eq!(i2, 2);

        let i3 = subtrie_page.insert_value(&[11; 1015][..]).unwrap();
        assert_eq!(i3, 3);

        subtrie_page.delete_value(i1).unwrap();
        assert_eq!(subtrie_page.num_cells(), 4);

        let i4 = subtrie_page.insert_value(&[11; 1000][..]).unwrap();
        assert_eq!(i4, 1);
        assert_eq!(subtrie_page.num_cells(), 4);
        let cell_pointer = subtrie_page.get_cell_pointer(i4).unwrap();
        assert_eq!(cell_pointer.length(), 1000);
        assert_eq!(cell_pointer.offset(), 2020); // 2020 = 1020 + 1000
    }

    #[test]
    fn test_allocate_reuse_deleted_spaces() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();

        let i0 = subtrie_page.insert_value(&[11; 1020][..]).unwrap();
        assert_eq!(i0, 0);

        let i1 = subtrie_page.insert_value(&[11; 1020][..]).unwrap();
        assert_eq!(i1, 1);

        let i2 = subtrie_page.insert_value(&[11; 1020][..]).unwrap();
        assert_eq!(i2, 2);

        let i3 = subtrie_page.insert_value(&[11; 1015][..]).unwrap();
        assert_eq!(i3, 3);

        subtrie_page.delete_value(i1).unwrap();
        assert_eq!(subtrie_page.num_cells(), 4);
        subtrie_page.delete_value(i2).unwrap();
        assert_eq!(subtrie_page.num_cells(), 4);

        let i4 = subtrie_page.insert_value(&[11; 1500][..]).unwrap();
        assert_eq!(i4, 1);
        assert_eq!(subtrie_page.num_cells(), 4);
        let cell_pointer = subtrie_page.get_cell_pointer(i4).unwrap();
        assert_eq!(cell_pointer.length(), 1500);
        assert_eq!(cell_pointer.offset(), 2520); // 2520 = 1020 + 1500

        let i5 = subtrie_page.insert_value(&[11; 100][..]).unwrap();
        assert_eq!(i5, 2);
        assert_eq!(subtrie_page.num_cells(), 4);
        let cell_pointer = subtrie_page.get_cell_pointer(i5).unwrap();
        assert_eq!(cell_pointer.length(), 100);
        assert_eq!(cell_pointer.offset(), 2620); // 2620 = 2520 + 100

        let i6 = subtrie_page.insert_value(&[11; 100][..]).unwrap();
        assert_eq!(i6, 4);
        assert_eq!(subtrie_page.num_cells(), 5);
        let cell_pointer = subtrie_page.get_cell_pointer(i6).unwrap();
        assert_eq!(cell_pointer.length(), 100);
        assert_eq!(cell_pointer.offset(), 2720); // 2720 = 2620 + 100
    }
}
