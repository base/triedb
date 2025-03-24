use fmmap::{MmapFileExt, MmapFileMut, MmapFileMutExt, Options};

use crate::{
    page::{Page, PAGE_SIZE, RO, RW},
    snapshot::SnapshotId,
};

use super::{PageError, PageId, PageManager};

#[derive(Debug)]
pub struct FmmapPageManager {
    mmap: MmapFileMut,
    next_page_id: PageId,
}

impl FmmapPageManager {
    pub fn open(file_path: &str) -> Result<Self, PageError> {
        let options = Options::new().read(true).write(true).create(true).truncate(false);
        let mmap = MmapFileMut::open_with_options(file_path, options).map_err(PageError::IO2)?;
        let file_len = mmap.len();
        let page_count = file_len / PAGE_SIZE;
        Ok(Self { mmap, next_page_id: page_count as PageId })
    }
}

impl PageManager for FmmapPageManager {
    fn get<'p>(
        &self,
        _snapshot_id: SnapshotId,
        page_id: PageId,
    ) -> Result<Page<'p, RO>, super::PageError> {
        let offset = page_id as usize * PAGE_SIZE;
        let page_data = self.mmap.slice_mut(offset, PAGE_SIZE);
        let page_array = page_data.try_into().map_err(PageError::TryFromSliceError)?;
        Ok(Page::new_ro(page_id, page_array))
    }

    fn get_mut<'p>(
        &mut self,
        snapshot_id: crate::snapshot::SnapshotId,
        page_id: super::PageId,
    ) -> Result<Page<'p, RW>, super::PageError> {
        todo!()
    }

    fn allocate<'p>(
        &mut self,
        snapshot_id: crate::snapshot::SnapshotId,
    ) -> Result<Page<'p, RW>, super::PageError> {
        todo!()
    }

    fn resize(&mut self, new_page_count: super::PageId) -> Result<(), super::PageError> {
        todo!()
    }

    fn size(&self) -> u32 {
        todo!()
    }

    fn commit(&mut self, snapshot_id: crate::snapshot::SnapshotId) -> Result<(), super::PageError> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_allocate_get() {
        todo!()
    }
}
