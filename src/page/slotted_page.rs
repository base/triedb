use std::cmp::max;
use std::fmt::Debug;

use super::{Page, PageError, PageMut, ReadablePage, WritablePage, PAGE_DATA_SIZE};

pub mod cell_pointer;
use cell_pointer::CellPointer;

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
pub struct SlottedPage<'p> {
    page: Page<'p>,
}

impl<'p> SlottedPage<'p> {
    // Returns the number of cells in the page, which may include deleted cells.
    fn num_cells(&'p self) -> u8 {
        num_cells(&self.page)
    }

    // Returns the cell pointer at the given index.
    fn get_cell_pointer(&self, index: u8) -> Result<CellPointer, PageError> {
        get_cell_pointer(&self.page, index)
    }
}

impl<'p, 'v, V: Value<'v>> SlottedStorage<'p, 'v, V> for SlottedPage<'p> {
    type Error = PageError;

    fn get_value(&'v self, index: u8) -> Result<V, Self::Error>
    where
        'p: 'v,
    {
        get_value(&self.page, index)
    }
}

// A mutable slotted page.
pub struct SlottedPageMut<'p> {
    page: PageMut<'p>,
}

impl<'p> SlottedPageMut<'p> {
    // Returns the value at the given index.
    pub fn get_value<'v, V: Value<'v>>(&'p self, index: u8) -> Result<V, PageError>
    where
        'p: 'v,
    {
        get_value(&self.page, index)
    }

    // Sets the value at the given index.
    pub fn set_value<'v, V: Value<'v>>(&mut self, index: u8, value: V) -> Result<(), PageError>
    where
        'p: 'v,
    {
        let cell_pointer = self.get_cell_pointer(index)?;
        let offset = cell_pointer.offset();
        let length = cell_pointer.length();
        let start_index = (4096 - offset - length) as usize;
        let end_index = (4096 - offset) as usize;
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
            set_num_cells(&mut self.page, new_num_cells);
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
        if num_cells == 255 {
            return Err(PageError::NoFreeCells);
        }
        Ok(num_cells)
    }

    // Allocates a cell pointer at the given index with the given length and returns the cell pointer.
    fn allocate_cell_pointer(&mut self, index: u8, length: u16) -> Result<CellPointer, PageError> {
        // TODO: defragment the page if necessary, or attempt to reuse deleted cells

        // for now, always allocate from the contiguous free space
        let num_cells = self.num_cells();
        let mut max_offset = 0;
        for i in 0..num_cells {
            let offset = self.get_cell_pointer(i)?.offset();
            if offset > max_offset {
                max_offset = offset;
            }
        }

        let new_num_cells = max(num_cells, index + 1);

        let offset = max_offset + length;
        if offset as usize > self.page.contents().len() - new_num_cells as usize * 3 - 1 {
            return Err(PageError::PageIsFull);
        }

        if new_num_cells > num_cells {
            set_num_cells(&mut self.page, new_num_cells);
        }

        return self.set_cell_pointer(index, offset, length);
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

    // Returns the number of cells in the page, which may include deleted cells.
    fn num_cells(&self) -> u8 {
        num_cells(&self.page)
    }

    // Returns the cell pointer at the given index.
    fn get_cell_pointer(&'p self, index: u8) -> Result<CellPointer, PageError> {
        get_cell_pointer(&self.page, index)
    }
}

// Returns the number of cells in the page, which may include deleted cells.
fn num_cells<P: ReadablePage>(page: &P) -> u8 {
    page.contents()[0]
}

// Sets the number of cells in the page.
fn set_num_cells<P: WritablePage>(page: &mut P, num_cells: u8) {
    page.contents_mut()[0] = num_cells;
}

// Returns the cell pointer at the given index.
fn get_cell_pointer<P: ReadablePage>(page: &P, index: u8) -> Result<CellPointer, PageError> {
    if index >= num_cells(page) {
        return Err(PageError::InvalidCellPointer);
    }
    let start_index = 1 + 3 * (index as usize);
    let end_index = start_index + 3;
    let data = &page.contents()[start_index..end_index];
    Ok(data.try_into()?)
}

// Returns the value at the given index.
fn get_value<'p, P: ReadablePage, V: Value<'p>>(page: &'p P, index: u8) -> Result<V, PageError> {
    let cell_pointer = get_cell_pointer(page, index)?;
    if cell_pointer.is_deleted() {
        return Err(PageError::InvalidCellPointer);
    }

    let offset = cell_pointer.offset();
    let length = cell_pointer.length();

    let start_index = (PAGE_DATA_SIZE as u16 - offset - length) as usize;
    let end_index = (PAGE_DATA_SIZE as u16 - offset) as usize;
    let data = &page.contents()[start_index..end_index];
    data.try_into().map_err(|_| PageError::InvalidCellPointer)
}

impl<'p> From<SlottedPageMut<'p>> for SlottedPage<'p> {
    fn from(page: SlottedPageMut<'p>) -> Self {
        Self {
            page: page.page.into(),
        }
    }
}

impl<'p> TryFrom<Page<'p>> for SlottedPage<'p> {
    type Error = PageError;

    fn try_from(page: Page<'p>) -> Result<Self, Self::Error> {
        Ok(Self { page })
    }
}

impl<'p> TryFrom<PageMut<'p>> for SlottedPageMut<'p> {
    type Error = PageError;

    fn try_from(page: PageMut<'p>) -> Result<Self, Self::Error> {
        Ok(Self { page })
    }
}

#[cfg(test)]
mod tests {
    use crate::page::PAGE_SIZE;

    use super::*;

    #[test]
    fn test_allocate_get_delete_cell_pointer() {
        let mut data = [0; PAGE_SIZE];
        let page = PageMut::new(42, 123, &mut data);
        let mut subtrie_page = SlottedPageMut::try_from(page).unwrap();
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
}
