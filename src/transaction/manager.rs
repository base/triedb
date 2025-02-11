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
    pub(crate) fn remove_transaction(&mut self, snapshot_id: SnapshotId, is_writer: bool) -> Result<(), ()> {
        let index = self.open_txs.binary_search(&snapshot_id).unwrap();
        self.open_txs.remove(index);
        if is_writer {
            self.has_writer = false;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_begin() {
        let mut manager = TransactionManager::new();
        let ro_snapshot_id = manager.begin_ro(1).unwrap();
        let rw_snapshot_id = manager.begin_rw(1).unwrap();
        assert_eq!(ro_snapshot_id, 1);
        assert_eq!(rw_snapshot_id, 1);

        let ro_snapshot_id = manager.begin_ro(2).unwrap();
        assert_eq!(ro_snapshot_id, 1);
    }

    #[test]
    #[should_panic]
    fn test_begin_rw_when_has_writer() {
        let mut manager = TransactionManager::new();
        manager.begin_rw(1).unwrap();
        manager.begin_rw(2).unwrap();
    }

    #[test]
    fn test_remove_transaction() {
        let mut manager = TransactionManager::new();
        assert_eq!(manager.begin_rw(1).unwrap(), 1);
        assert_eq!(manager.begin_ro(2).unwrap(), 1);
        assert_eq!(manager.begin_ro(3).unwrap(), 1);

        assert_eq!(manager.remove_transaction(1, true).unwrap(), ());
        assert_eq!(manager.begin_ro(4).unwrap(), 2);
        assert_eq!(manager.begin_rw(5).unwrap(), 2);

        assert_eq!(manager.remove_transaction(2, false).unwrap(), ());
        assert_eq!(manager.remove_transaction(3, false).unwrap(), ());
        assert_eq!(manager.remove_transaction(4, false).unwrap(), ());
        assert_eq!(manager.remove_transaction(5, true).unwrap(), ());

        assert_eq!(manager.begin_ro(6).unwrap(), 6);
        assert_eq!(manager.remove_transaction(6, false).unwrap(), ());
    }

    #[test]
    #[should_panic]
    fn test_remove_nonexistent_transaction() {
        let mut manager = TransactionManager::new();
        manager.remove_transaction(1, true).unwrap();
    }
}
