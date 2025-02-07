use std::fmt::Debug;
use crate::snapshot::SnapshotId;

#[derive(Debug)]
pub struct TransactionManager {
    has_writer: bool,
    open_txs: Vec<SnapshotId>,
}

impl TransactionManager {
    pub fn new() -> Self {
        Self { has_writer: false, open_txs: Vec::new() }
    }

    pub fn begin_rw(&mut self, snapshot_id: SnapshotId) -> Result<SnapshotId, ()> {
        // only allow one writable transaction at a time
        if self.has_writer {
            return Err(());
        }
        self.has_writer = true;
        self.add_tx_handle(snapshot_id)
    }

    pub fn begin_ro(&mut self, snapshot_id: SnapshotId) -> Result<SnapshotId, ()> {
        self.add_tx_handle(snapshot_id)
    }

    fn add_tx_handle(&mut self, snapshot_id: SnapshotId) -> Result<SnapshotId, ()> {
        self.open_txs.push(snapshot_id);
        self.open_txs.sort_unstable();
        Ok(*self.open_txs.first().unwrap())
    }

    // Removes a transaction from the list of open transactions
    pub(crate) fn remove_transaction(&mut self, snapshot_id: SnapshotId) -> Result<(), ()> {
        let index = self.open_txs.binary_search(&snapshot_id).unwrap();
        self.open_txs.remove(index);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use memmap2::MmapMut;

    use super::*;
    use crate::page::{MmapPageManager, OrphanPageManager, ReadablePage, RootPage, WritablePage};
    #[test]
    fn test_rw_transaction() {
        // let mmap = MmapMut::map_anon(10*4096).unwrap();
        // let mmap_page_manager = MmapPageManager::new(mmap, 2);
        // let orphan_manager = OrphanPageManager::new();
        // let manager = TransactionManager::new(StorageEngine::new(0, 0, 0, mmap_page_manager, orphan_manager));
        // let mut rw_tx = manager.begin_rw().unwrap();
        // let ro_tx = manager.begin_ro().unwrap();

        // println!("rw_tx: {:?}", rw_tx.storage_engine.snapshot_id());

        // let page0_ro = rw_tx.storage_engine.get_page(0).unwrap();
        // println!("page0_ro: {:?}", page0_ro.contents()[0]);

        // let mut page0_mut = rw_tx.storage_engine.get_mut_page(0).unwrap();
        // println!("page0_mut: {:?}", page0_mut.contents()[0]);

        // page0_mut.contents_mut()[0] = 1;

        // println!("page0_ro: {:?}", page0_ro.contents()[0]);
        // println!("page0_mut: {:?}", page0_mut.contents()[0]);

        // rw_tx.storage_engine.commit().unwrap();

        // println!("page0_ro: {:?}", page0_ro.contents()[0]);
        // println!("page0_mut: {:?}", page0_mut.contents()[0]);

        // rw_tx.commit().unwrap();

        // let root_page: RootPage = ro_tx.storage_engine.get_page(1).unwrap().try_into().unwrap();
        // println!("root_page: {:?} {:?}", root_page.snapshot_id(), root_page.state_root());
    }
}
