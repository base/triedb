use fmmap::{MmapFileMut, Options};

use super::{PageError, PageManager};

#[derive(Debug)]
pub struct FmmapPageManager {}

impl FmmapPageManager {
    pub fn open(file_path: &str) -> Result<Self, PageError> {
        let options = Options::new().read(true).write(true).create(true).truncate(false);
        let mut file =
            MmapFileMut::open_with_options(file_path, options).map_err(PageError::IO2)?;
        Ok(Self {})
    }
}

impl PageManager for FmmapPageManager {
    fn get<'p>(
        &self,
        snapshot_id: crate::snapshot::SnapshotId,
        page_id: super::PageId,
    ) -> Result<crate::page::Page<'p, crate::page::RO>, super::PageError> {
        todo!()
    }

    fn get_mut<'p>(
        &mut self,
        snapshot_id: crate::snapshot::SnapshotId,
        page_id: super::PageId,
    ) -> Result<crate::page::Page<'p, crate::page::RW>, super::PageError> {
        todo!()
    }

    fn allocate<'p>(
        &mut self,
        snapshot_id: crate::snapshot::SnapshotId,
    ) -> Result<crate::page::Page<'p, crate::page::RW>, super::PageError> {
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
