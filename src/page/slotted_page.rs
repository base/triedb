use std::cmp::max;

use crate::storage::value::{Value, ValueRef};

use super::{
    page::{PageKind, RO, RW},
    Page, PageError, PageId, PAGE_DATA_SIZE,
};

pub mod cell_pointer;
use cell_pointer::CellPointer;

const MAX_NUM_CELLS: u8 = 255; // With 1 byte for the number of cells, the maximum number of cells is 255.

// A page that contains a sequence of pointers to variable-length values,
// where the pointers are stored in a contiguous array of 3-byte cell pointers from the
// beginning of the page, and the values are added from the end of the page.
pub struct SlottedPage<'p, P: PageKind> {
    page: Page<'p, P>,
}

impl<P: PageKind> SlottedPage<'_, P> {
    pub fn page_id(&self) -> PageId {
        self.page.page_id()
    }

    // Get a reference to a value
    pub fn get_value_ref<'v, V: ValueRef<'v>>(&'v self, index: u8) -> Result<V, PageError> {
        let cell_pointer = self.get_cell_pointer(index)?;
        if cell_pointer.is_deleted() {
            return Err(PageError::InvalidCellPointer);
        }

        let offset = cell_pointer.offset();
        let length = cell_pointer.length();
        let start_index = (PAGE_DATA_SIZE as u16 - offset) as usize;
        let data = &self.page.contents()[start_index..start_index + length as usize];

        V::from_bytes(data).map_err(|_| PageError::InvalidValue)
    }

    // Get an owned value
    pub fn get_value<V: Value>(&self, index: u8) -> Result<V, PageError> {
        let cell_pointer = self.get_cell_pointer(index)?;
        if cell_pointer.is_deleted() {
            return Err(PageError::InvalidCellPointer);
        }

        let offset = cell_pointer.offset();
        let length = cell_pointer.length();
        let start_index = (PAGE_DATA_SIZE as u16 - offset) as usize;
        let data = &self.page.contents()[start_index..start_index + length as usize];

        V::from_bytes(data).map_err(|_| PageError::InvalidValue)
    }

    pub fn num_free_bytes(&self) -> usize {
        self.num_free_bytes_with_cell_count(self.num_cells())
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

    fn cell_pointers_iter(&self) -> impl Iterator<Item = CellPointer> {
        self.page.contents()[1..=3 * self.num_cells() as usize]
            .chunks(3)
            .map(|chunk| chunk.try_into().unwrap())
    }

    fn num_free_bytes_with_cell_count(&self, num_cells: u8) -> usize {
        let total_occupied_space = self
            .cell_pointers_iter()
            .filter(|cp| !cp.is_deleted())
            .map(|cp| cp.length())
            .sum::<u16>();

        self.page.contents().len() - total_occupied_space as usize - 3 * num_cells as usize - 1
    }

    fn num_dead_bytes(&self, num_cells: u8) -> usize {
        let total_bytes = self.page.contents().len();
        let free_bytes = self.num_free_bytes_with_cell_count(num_cells);
        let used_bytes: usize = self
            .cell_pointers_iter()
            .map(|cp| cp.length() as usize)
            .sum();
        total_bytes - free_bytes - used_bytes - 1 - 3 * num_cells as usize
    }
}

impl<P: PageKind> std::fmt::Debug for SlottedPage<'_, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let num_cells = self.num_cells();
        write!(f, "SlottedPage {{ page_id: {}, num_cells: {}, cell_pointers: {:?}, free_bytes: {}, dead_bytes: {} }}",
            self.page_id(),
            self.num_cells(),
            self.cell_pointers_iter().collect::<Vec<CellPointer>>(),
            self.num_free_bytes_with_cell_count(num_cells),
            self.num_dead_bytes(num_cells)
        )
    }
}

impl SlottedPage<'_, RW> {
    // Sets the value at the given index.
    pub fn set_value<V: Value>(&mut self, index: u8, value: V) -> Result<(), PageError> {
        let cell_pointer = self.get_cell_pointer(index)?;
        let value_length = value.size();

        let mut offset = cell_pointer.offset();
        let mut length = cell_pointer.length();

        if value_length > length as usize {
            // the value is larger than the current cell, so we need to allocate a new cell
            let cell_pointer = self.allocate_cell_pointer(index, value_length as u16)?;
            // TODO: if error is PageIsFull, we should split the page
            // This is the place when a branch node go from 8 -> 9 children increase size from 300 -> 596

            (offset, length) = (cell_pointer.offset(), cell_pointer.length());
        } else if value_length < length as usize {
            // the value is smaller than the current cell, so we can shrink the cell in place
            length = value_length as u16;
            self.set_cell_pointer(index, offset, length)?;
        }

        let start_index = (PAGE_DATA_SIZE as u16 - offset) as usize;
        let end_index = (PAGE_DATA_SIZE as u16 - offset + length) as usize;
        let data = &mut self.page.contents_mut()[start_index..end_index];
        value
            .serialize_into(data)
            .map_err(|_| PageError::InvalidValue)?;
        Ok(())
    }

    // Inserts a value into the page and returns the index of the new value.
    pub fn insert_value<V: Value>(&mut self, value: V) -> Result<u8, PageError> {
        let cell_index = self.next_free_cell_index()?;
        let value_length = value.size();
        let cell_pointer = self.allocate_cell_pointer(cell_index, value_length as u16)?;

        let offset = cell_pointer.offset();
        let length = cell_pointer.length();
        let start_index = (PAGE_DATA_SIZE as u16 - offset) as usize;
        let end_index = (PAGE_DATA_SIZE as u16 - offset + length) as usize;
        let data = &mut self.page.contents_mut()[start_index..end_index];
        value
            .serialize_into(data)
            .map_err(|_| PageError::InvalidValue)?;
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
                self.set_cell_pointer(index, offset, length)
            }
            None => match self.defragment(index, length)? {
                true => self.allocate_cell_pointer(index, length),
                false => Err(PageError::PageIsFull),
            },
        }
    }

    fn defragment(&mut self, index: u8, additional_slot_length: u16) -> Result<bool, PageError> {
        let num_cells = self.num_cells();

        let total_occupied_space = self
            .cell_pointers_iter()
            .enumerate()
            .filter(|(i, cp)| *i != index as usize && !cp.is_deleted())
            .map(|(_, cp)| cp.length())
            .sum::<u16>();

        let new_num_cells = max(num_cells, index + 1);
        if (total_occupied_space + additional_slot_length + new_num_cells as u16 * 3 + 1) as usize
            > PAGE_DATA_SIZE
        {
            return Ok(false);
        }

        let mut cell_pointers = self
            .cell_pointers_iter()
            .enumerate()
            .filter(|(i, cp)| *i != index as usize && !cp.is_deleted())
            .map(|(i, cp)| (i, cp.offset(), cp.length()))
            .collect::<Vec<_>>();

        // sort by offset
        cell_pointers.sort_by(|a, b| a.1.cmp(&b.1));

        let mut last_start = 0;
        let mut last_offset = 0;
        for (idx, offset, len) in cell_pointers {
            let start = offset - len;
            if start == last_start {
                last_offset = offset;
                continue;
            }

            let start_index = (PAGE_DATA_SIZE as u16 - offset) as usize;
            let end_index = start_index + len as usize;

            let new_offset = last_offset + len;
            self.set_cell_pointer(idx as u8, new_offset, len)?;

            let new_start_index = (PAGE_DATA_SIZE as u16 - new_offset) as usize;
            self.page
                .contents_mut()
                .copy_within(start_index..end_index, new_start_index);

            last_start = new_offset - len;
            last_offset = new_offset;
        }

        Ok(true)
    }

    // Finds a free space with length in the page. Returns slotted page offset if found.
    fn find_available_slot(&self, index: u8, length: u16) -> Result<Option<u16>, PageError> {
        match self.find_available_slot_in_used_space(index, length)? {
            Some(offset) => Ok(Some(offset)),
            None => self.find_available_slot_in_remaining_space(index, length),
        }
    }

    fn find_available_slot_in_used_space(
        &self,
        index: u8,
        length: u16,
    ) -> Result<Option<u16>, PageError> {
        let num_cells = self.num_cells();
        let new_num_cells = max(num_cells, index + 1);
        let header_size = new_num_cells as usize * 3 + 1;
        let mut used_space = Vec::new();
        for i in 0..num_cells {
            let cp = self.get_cell_pointer(i)?;
            if cp.is_deleted() {
                continue;
            }
            // ensure existing offsets do not overlap with the header
            if cp.offset() as usize + header_size > self.page.contents().len() {
                return Ok(None);
            }
            used_space.push((cp.offset() - cp.length(), cp.offset()));
        }

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
            // skip the cell we are allocating for, as its space will be freed up
            if i == index {
                continue;
            }
            let cp = self.get_cell_pointer(i)?;
            if !cp.is_deleted() {
                // Only consider non-deleted cells
                let offset = cp.offset();
                if offset > max_offset {
                    max_offset = offset;
                }
            }
        }

        let offset = max_offset + length;
        let header_size = new_num_cells as usize * 3 + 1;
        let available_space = self.page.contents().len() - header_size;

        if offset as usize > available_space {
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

        let v1 = String::from("hello");
        let i1 = subtrie_page.insert_value(v1.clone()).unwrap();
        assert_eq!(i1, 0);

        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        let v2 = String::from("world");
        let i2 = subtrie_page.insert_value(v2.clone()).unwrap();
        assert_eq!(i2, 1);

        let v: String = subtrie_page.get_value(i2).unwrap();
        assert_eq!(v, v2);

        // ensure the first cell is not modified
        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        // sanity check the page
        assert_eq!(subtrie_page.num_cells(), 2);
    }

    #[test]
    fn test_insert_set_value() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();

        let v1 = String::from("hello");
        let i1 = subtrie_page.insert_value(v1.clone()).unwrap();
        assert_eq!(i1, 0);

        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        let v2 = String::from("world");
        subtrie_page.set_value(i1, v2.clone()).unwrap();

        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v2);
    }

    #[test]
    fn test_set_value_same_length() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();

        let v1 = String::from("hello");
        let i1 = subtrie_page.insert_value(v1.clone()).unwrap();
        assert_eq!(i1, 0);

        let cell_pointer = subtrie_page.get_cell_pointer(i1).unwrap();
        assert_eq!(cell_pointer.length(), 5);
        assert_eq!(cell_pointer.offset(), 5);

        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        let v2 = String::from("world");
        subtrie_page.set_value(i1, v2.clone()).unwrap();

        let cell_pointer = subtrie_page.get_cell_pointer(i1).unwrap();
        assert_eq!(cell_pointer.length(), 5);
        assert_eq!(cell_pointer.offset(), 5);

        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v2);

        assert_eq!(subtrie_page.num_cells(), 1);
    }

    #[test]
    fn test_set_value_shrink() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();

        let v1 = String::from("hello");
        let i1 = subtrie_page.insert_value(v1.clone()).unwrap();
        assert_eq!(i1, 0);

        let cell_pointer = subtrie_page.get_cell_pointer(i1).unwrap();
        assert_eq!(cell_pointer.length(), 5);
        assert_eq!(cell_pointer.offset(), 5);

        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        // shrink the value IN-PLACE to one character
        // this behavior may change in the future
        let v2 = String::from("w");
        subtrie_page.set_value(i1, v2.clone()).unwrap();

        let cell_pointer = subtrie_page.get_cell_pointer(i1).unwrap();
        assert_eq!(cell_pointer.length(), 1);
        assert_eq!(cell_pointer.offset(), 5);

        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v2);

        assert_eq!(subtrie_page.num_cells(), 1);
    }

    #[test]
    fn test_set_value_shrink_with_neighbors() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();

        let v1 = String::from("one");
        let i1 = subtrie_page.insert_value(v1.clone()).unwrap();
        assert_eq!(i1, 0);

        let cell_pointer = subtrie_page.get_cell_pointer(i1).unwrap();
        assert_eq!(cell_pointer.length(), 3);
        assert_eq!(cell_pointer.offset(), 3);

        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        let v2 = String::from("two");
        let i2 = subtrie_page.insert_value(v2.clone()).unwrap();
        assert_eq!(i2, 1);

        let cell_pointer = subtrie_page.get_cell_pointer(i2).unwrap();
        assert_eq!(cell_pointer.length(), 3);
        assert_eq!(cell_pointer.offset(), 6);

        let v: String = subtrie_page.get_value(i2).unwrap();
        assert_eq!(v, v2);

        let v3 = String::from("three");
        let i3 = subtrie_page.insert_value(v3.clone()).unwrap();
        assert_eq!(i3, 2);

        let cell_pointer = subtrie_page.get_cell_pointer(i3).unwrap();
        assert_eq!(cell_pointer.length(), 5);
        assert_eq!(cell_pointer.offset(), 11);

        let v: String = subtrie_page.get_value(i3).unwrap();
        assert_eq!(v, v3);

        // shrink the middle value to two characters. It should retain the same offset.
        let v4 = String::from("tw");
        subtrie_page.set_value(i2, v4.clone()).unwrap();

        let cell_pointer = subtrie_page.get_cell_pointer(i2).unwrap();
        assert_eq!(cell_pointer.length(), 2);
        assert_eq!(cell_pointer.offset(), 6);

        let v: String = subtrie_page.get_value(i2).unwrap();
        assert_eq!(v, v4);

        assert_eq!(subtrie_page.num_cells(), 3);

        // ensure the neighboring cells are not modified
        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        let v: String = subtrie_page.get_value(i3).unwrap();
        assert_eq!(v, v3);
    }

    #[test]
    fn test_set_value_grow() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();

        let v1 = String::from("this");
        let i1 = subtrie_page.insert_value(v1.clone()).unwrap();
        assert_eq!(i1, 0);

        let cell_pointer = subtrie_page.get_cell_pointer(i1).unwrap();
        assert_eq!(cell_pointer.length(), 4);
        assert_eq!(cell_pointer.offset(), 4);

        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        let v2 = String::from("is a test, this is only a test");
        subtrie_page.set_value(i1, v2.clone()).unwrap();

        let cell_pointer = subtrie_page.get_cell_pointer(i1).unwrap();
        assert_eq!(cell_pointer.length(), 30);
        assert_eq!(cell_pointer.offset(), 30);

        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v2);

        assert_eq!(subtrie_page.num_cells(), 1);
    }

    #[test]
    fn test_set_value_grow_with_neighbors() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();

        let v1 = String::from("one");
        let i1 = subtrie_page.insert_value(v1.clone()).unwrap();
        assert_eq!(i1, 0);

        let cell_pointer = subtrie_page.get_cell_pointer(i1).unwrap();
        assert_eq!(cell_pointer.length(), 3);
        assert_eq!(cell_pointer.offset(), 3);

        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        let v2 = String::from("two");
        let i2 = subtrie_page.insert_value(v2.clone()).unwrap();
        assert_eq!(i2, 1);

        let cell_pointer = subtrie_page.get_cell_pointer(i2).unwrap();
        assert_eq!(cell_pointer.length(), 3);
        assert_eq!(cell_pointer.offset(), 6);

        let v: String = subtrie_page.get_value(i2).unwrap();
        assert_eq!(v, v2);

        let v3 = String::from("three");
        let i3 = subtrie_page.insert_value(v3.clone()).unwrap();
        assert_eq!(i3, 2);

        let cell_pointer = subtrie_page.get_cell_pointer(i3).unwrap();
        assert_eq!(cell_pointer.length(), 5);
        assert_eq!(cell_pointer.offset(), 11);

        let v: String = subtrie_page.get_value(i3).unwrap();
        assert_eq!(v, v3);

        // grow the middle value to 19 characters. It will need a new offset.
        let v4 = String::from("nineteen characters");
        subtrie_page.set_value(i2, v4.clone()).unwrap();

        let cell_pointer = subtrie_page.get_cell_pointer(i2).unwrap();
        assert_eq!(cell_pointer.length(), 19);
        assert_eq!(cell_pointer.offset(), 30);

        let v: String = subtrie_page.get_value(i2).unwrap();
        assert_eq!(v, v4);

        assert_eq!(subtrie_page.num_cells(), 3);

        // ensure the neighboring cells are not modified
        let v: String = subtrie_page.get_value(i1).unwrap();
        assert_eq!(v, v1);

        let v: String = subtrie_page.get_value(i3).unwrap();
        assert_eq!(v, v3);
    }

    #[test]
    fn test_allocate_get_delete_cell_pointer() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();
        let cell_index = subtrie_page.insert_value(String::from("foo")).unwrap();
        assert_eq!(cell_index, 0);
        assert_eq!(subtrie_page.num_cells(), 1);
        assert_eq!(subtrie_page.get_cell_pointer(0).unwrap().length(), 3);
        assert_eq!(subtrie_page.get_cell_pointer(0).unwrap().offset(), 3);

        let cell_index = subtrie_page.insert_value(String::from("bar")).unwrap();
        assert_eq!(cell_index, 1);
        assert_eq!(subtrie_page.num_cells(), 2);
        assert_eq!(subtrie_page.get_cell_pointer(1).unwrap().length(), 3);
        assert_eq!(subtrie_page.get_cell_pointer(1).unwrap().offset(), 6);

        let cell_index = subtrie_page
            .insert_value(String::from_iter(&['8'; 88]))
            .unwrap();
        assert_eq!(cell_index, 2);
        assert_eq!(subtrie_page.num_cells(), 3);
        assert_eq!(subtrie_page.get_cell_pointer(2).unwrap().length(), 88);
        assert_eq!(subtrie_page.get_cell_pointer(2).unwrap().offset(), 94);

        let cell_index = subtrie_page
            .insert_value(String::from_iter(&['8'; 88]))
            .unwrap();
        assert_eq!(cell_index, 3);
        assert_eq!(subtrie_page.num_cells(), 4);
        assert_eq!(subtrie_page.get_cell_pointer(3).unwrap().length(), 88);
        assert_eq!(subtrie_page.get_cell_pointer(3).unwrap().offset(), 182);

        let cell_index = subtrie_page
            .insert_value(String::from_iter(&['8'; 88]))
            .unwrap();
        assert_eq!(cell_index, 4);
        assert_eq!(subtrie_page.num_cells(), 5);
        assert_eq!(subtrie_page.get_cell_pointer(4).unwrap().length(), 88);
        assert_eq!(subtrie_page.get_cell_pointer(4).unwrap().offset(), 270);

        // remaining space should be 4088 - 1 - 3*5 - 270 = 3892
        // still need enough space for the new cell pointer (3 bytes), so this should fail
        let cell_index = subtrie_page.insert_value(String::from_iter(&['a'; 3802]));
        assert!(cell_index.is_err());
        assert!(matches!(cell_index, Err(PageError::PageIsFull)));
        assert_eq!(subtrie_page.num_cells(), 5);

        let cell_index = subtrie_page.insert_value(String::from_iter(&['b'; 3801]));
        assert!(cell_index.is_err());
        assert!(matches!(cell_index, Err(PageError::PageIsFull)));
        assert_eq!(subtrie_page.num_cells(), 5);

        let cell_index = subtrie_page.insert_value(String::from_iter(&['c'; 3800]));
        assert!(cell_index.is_err());
        assert!(matches!(cell_index, Err(PageError::PageIsFull)));
        assert_eq!(subtrie_page.num_cells(), 5);

        let cell_index = subtrie_page
            .insert_value(String::from_iter(&['d'; 3799]))
            .unwrap();
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
        let cell_index = subtrie_page
            .insert_value(String::from_iter(&['x'; 4084]))
            .unwrap();
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

        let i0 = subtrie_page
            .insert_value(String::from_iter(&['a'; 1020]))
            .unwrap();
        assert_eq!(i0, 0);

        let i1 = subtrie_page
            .insert_value(String::from_iter(&['b'; 1020]))
            .unwrap();
        assert_eq!(i1, 1);

        let i2 = subtrie_page
            .insert_value(String::from_iter(&['c'; 1020]))
            .unwrap();
        assert_eq!(i2, 2);

        let i3 = subtrie_page
            .insert_value(String::from_iter(&['d'; 1015]))
            .unwrap();
        assert_eq!(i3, 3);

        subtrie_page.delete_value(i1).unwrap();
        assert_eq!(subtrie_page.num_cells(), 4);

        let i4 = subtrie_page
            .insert_value(String::from_iter(&['e'; 1000]))
            .unwrap();
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

        // bytes 0-12 are used by the header, and the next 4072 are used by the first 4 cells
        // this sums up to 4085 bytes, which allows for one more pointer to be added later
        // without defragmenting the page.

        let i0 = subtrie_page
            .insert_value(String::from_iter(&['a'; 1020]))
            .unwrap();
        assert_eq!(i0, 0);

        let i1 = subtrie_page
            .insert_value(String::from_iter(&['b'; 1020]))
            .unwrap();
        assert_eq!(i1, 1);

        let i2 = subtrie_page
            .insert_value(String::from_iter(&['c'; 1020]))
            .unwrap();
        assert_eq!(i2, 2);

        let i3 = subtrie_page
            .insert_value(String::from_iter(&['d'; 1012]))
            .unwrap();
        assert_eq!(i3, 3);

        subtrie_page.delete_value(i1).unwrap();
        assert_eq!(subtrie_page.num_cells(), 4);
        subtrie_page.delete_value(i2).unwrap();
        assert_eq!(subtrie_page.num_cells(), 4);

        let i4 = subtrie_page
            .insert_value(String::from_iter(&['e'; 1500]))
            .unwrap();
        assert_eq!(i4, 1);
        assert_eq!(subtrie_page.num_cells(), 4);
        let cell_pointer = subtrie_page.get_cell_pointer(i4).unwrap();
        assert_eq!(cell_pointer.length(), 1500);
        assert_eq!(cell_pointer.offset(), 2520); // 2520 = 1020 + 1500

        let i5 = subtrie_page
            .insert_value(String::from_iter(&['f'; 100]))
            .unwrap();
        assert_eq!(i5, 2);
        assert_eq!(subtrie_page.num_cells(), 4);
        let cell_pointer = subtrie_page.get_cell_pointer(i5).unwrap();
        assert_eq!(cell_pointer.length(), 100);
        assert_eq!(cell_pointer.offset(), 2620); // 2620 = 2520 + 100

        let i6 = subtrie_page
            .insert_value(String::from_iter(&['g'; 100]))
            .unwrap();
        assert_eq!(i6, 4);
        assert_eq!(subtrie_page.num_cells(), 5);
        let cell_pointer = subtrie_page.get_cell_pointer(i6).unwrap();
        assert_eq!(cell_pointer.length(), 100);
        assert_eq!(cell_pointer.offset(), 2720); // 2720 = 2620 + 100

        // this additional insertion forces the page to be defragmented to avoid overlapping with the header
        let i7 = subtrie_page
            .insert_value(String::from_iter(&['h'; 100]))
            .unwrap();
        assert_eq!(i7, 5);
        assert_eq!(subtrie_page.num_cells(), 6);
        let cell_pointer = subtrie_page.get_cell_pointer(i7).unwrap();
        assert_eq!(cell_pointer.length(), 100);
        assert_eq!(cell_pointer.offset(), 3832);
    }

    #[test]
    fn test_defragment_page() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut subtrie_page = SlottedPage::<RW>::try_from(page).unwrap();

        let i0 = subtrie_page
            .insert_value(String::from_iter(&['a'; 814]))
            .unwrap();
        assert_eq!(i0, 0);

        let i1 = subtrie_page
            .insert_value(String::from_iter(&['b'; 814]))
            .unwrap();
        assert_eq!(i1, 1);

        let i2 = subtrie_page
            .insert_value(String::from_iter(&['c'; 814]))
            .unwrap();
        assert_eq!(i2, 2);

        let i3 = subtrie_page
            .insert_value(String::from_iter(&['d'; 814]))
            .unwrap();
        assert_eq!(i3, 3);

        let i4 = subtrie_page
            .insert_value(String::from_iter(&['e'; 814]))
            .unwrap();
        assert_eq!(i4, 4);

        subtrie_page.delete_value(i1).unwrap();
        assert_eq!(subtrie_page.num_cells(), 5);
        subtrie_page.delete_value(i3).unwrap();
        assert_eq!(subtrie_page.num_cells(), 5);

        // should not be able to allocate anything larger than 1630 bytes (4088 - 1 - 3*5 - 814 - 814 - 814 = 1630)
        let cell_index = subtrie_page.insert_value(String::from_iter(&['f'; 1631]));
        assert!(cell_index.is_err());
        assert!(matches!(cell_index, Err(PageError::PageIsFull)));

        // should be able to allocate 1630 bytes
        let i5 = subtrie_page
            .insert_value(String::from_iter(&['g'; 1630]))
            .unwrap();
        assert_eq!(i5, 1);

        assert_eq!(
            subtrie_page.get_value::<String>(i0).unwrap(),
            String::from_iter(&['a'; 814])
        );
        assert_eq!(
            subtrie_page.get_value::<String>(i5).unwrap(),
            String::from_iter(&['g'; 1630])
        );
        assert_eq!(
            subtrie_page.get_value::<String>(i2).unwrap(),
            String::from_iter(&['c'; 814])
        );
        let v = subtrie_page.get_value::<String>(i3);
        assert!(v.is_err());
        assert!(matches!(v, Err(PageError::InvalidCellPointer)));

        assert_eq!(
            subtrie_page.get_value::<String>(i4).unwrap(),
            String::from_iter(&['e'; 814])
        );
    }

    #[test]
    fn test_defragment_page_cells_out_of_order() {
        let mut data = [0; PAGE_SIZE];
        let page = Page::new_rw_with_snapshot(42, 123, &mut data);
        let mut slotted_page = SlottedPage::<RW>::try_from(page).unwrap();

        slotted_page.set_num_cells(16);

        let initial_cell_pointers = [
            (595, 595),
            (762, 167),
            (1358, 168),
            (929, 167),
            (0, 0),
            (1860, 168),
            (2028, 168),
            (2195, 167),
            (2362, 167),
            (2530, 168),
            (2865, 167),
            (2698, 168),
            (3962, 167),
            (3795, 595),
            (3033, 167),
            (3200, 167),
        ];

        for (idx, (offset, length)) in initial_cell_pointers.iter().enumerate() {
            slotted_page
                .set_cell_pointer(idx as u8, *offset, *length)
                .unwrap();
        }

        slotted_page.defragment(4, 595).unwrap();

        let expected_cell_pointers = [
            (595, 595),
            (762, 167),
            (1097, 168),
            (929, 167),
            (0, 0),
            (1265, 168),
            (1433, 168),
            (1600, 167),
            (1767, 167),
            (1935, 168),
            (2270, 167),
            (2103, 168),
            (3366, 167),
            (3199, 595),
            (2437, 167),
            (2604, 167),
        ];

        assert_eq!(slotted_page.num_cells(), expected_cell_pointers.len() as u8);

        for (idx, (offset, length)) in expected_cell_pointers.into_iter().enumerate() {
            let cell_pointer = slotted_page.get_cell_pointer(idx as u8).unwrap();
            assert_eq!(cell_pointer.offset(), offset);
            assert_eq!(cell_pointer.length(), length);
        }
    }
}
