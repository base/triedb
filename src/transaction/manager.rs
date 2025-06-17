use crate::{snapshot::SnapshotId, transaction::TransactionError};
use std::{
    fmt::Debug,
    sync::atomic::{AtomicBool, Ordering},
};

#[derive(Debug)]
pub struct TransactionManager {
    has_writer: AtomicBool,
    open_txs: Vec<SnapshotId>,
}

impl Default for TransactionManager {
    fn default() -> Self {
        Self::new()
    }
}

impl TransactionManager {
    pub fn new() -> Self {
        Self { has_writer: false.into(), open_txs: Vec::new() }
    }

    pub fn min_snapshot_id(&self) -> Option<SnapshotId> {
        self.open_txs.iter().copied().min()
    }

    pub fn begin_rw(&mut self, snapshot_id: SnapshotId) -> Result<SnapshotId, TransactionError> {
        // only allow one writable transaction at a time
        loop {
            match self.has_writer.compare_exchange_weak(
                false,
                true,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                _ => (),
            }
        }

        self.open_txs.push(snapshot_id - 1);
        Ok(self.min_snapshot_id().unwrap())
    }

    pub fn begin_ro(&mut self, snapshot_id: SnapshotId) {
        self.open_txs.push(snapshot_id);
    }

    // Removes a transaction from the list of open transactions
    pub(crate) fn remove_tx(&mut self, snapshot_id: SnapshotId, is_writer: bool) {
        if is_writer {
            self.has_writer.store(false, Ordering::Relaxed);
        }

        let snapshot_id = if is_writer { snapshot_id - 1 } else { snapshot_id };
        let index =
            self.open_txs.iter().position(|&s| s == snapshot_id).expect("snapshot not found");
        self.open_txs.swap_remove(index);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_begin() {
        let mut manager = TransactionManager::new();
        assert_eq!(manager.min_snapshot_id(), None);

        manager.begin_ro(1);
        assert_eq!(manager.min_snapshot_id(), Some(1));

        assert_eq!(manager.begin_rw(1).unwrap(), 0);
        assert_eq!(manager.min_snapshot_id(), Some(0));

        manager.begin_ro(2);
        assert_eq!(manager.min_snapshot_id(), Some(0));
    }

    #[test]
    fn test_remove_transaction() {
        let mut manager = TransactionManager::new();
        assert_eq!(manager.min_snapshot_id(), None);

        assert_eq!(manager.begin_rw(1).unwrap(), 0);
        assert_eq!(manager.min_snapshot_id(), Some(0));

        manager.begin_ro(2);
        assert_eq!(manager.min_snapshot_id(), Some(0));
        manager.begin_ro(3);
        assert_eq!(manager.min_snapshot_id(), Some(0));

        manager.remove_tx(1, true);
        assert_eq!(manager.min_snapshot_id(), Some(2));

        manager.begin_ro(4);
        assert_eq!(manager.min_snapshot_id(), Some(2));

        assert_eq!(manager.begin_rw(5).unwrap(), 2);
        assert_eq!(manager.min_snapshot_id(), Some(2));

        manager.remove_tx(2, false);
        assert_eq!(manager.min_snapshot_id(), Some(3));
        manager.remove_tx(3, false);
        assert_eq!(manager.min_snapshot_id(), Some(4));
        manager.remove_tx(4, false);
        assert_eq!(manager.min_snapshot_id(), Some(4));
        manager.remove_tx(5, true);
        assert_eq!(manager.min_snapshot_id(), None);

        manager.begin_ro(6);
        assert_eq!(manager.min_snapshot_id(), Some(6));
        manager.remove_tx(6, false);
        assert_eq!(manager.min_snapshot_id(), None);
    }

    #[test]
    #[should_panic]
    fn test_remove_nonexistent_transaction() {
        let mut manager = TransactionManager::new();
        manager.remove_tx(1, true);
    }
}
