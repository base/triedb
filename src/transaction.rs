mod manager;

use std::{fmt::Debug, sync::RwLockReadGuard};

use crate::{database::Database, page::PageManager, snapshot::SnapshotId};
pub use manager::TransactionManager;
use sealed::sealed;

#[sealed]
pub trait TransactionKind: Debug {}

#[derive(Debug)]
pub struct RW {}

#[sealed]
impl TransactionKind for RW {}

#[derive(Debug)]
pub struct RO {}

#[sealed]
impl TransactionKind for RO {}

#[derive(Debug)]
pub struct Transaction<'db, K: TransactionKind, P: PageManager, L> {
    snapshot_id: SnapshotId,
    committed: bool,
    database: &'db Database<P>,
    lock: Option<RwLockReadGuard<'db, L>>,
    _marker: std::marker::PhantomData<K>,
}

impl<'db, K: TransactionKind, P: PageManager, L> Transaction<'db, K, P, L> {
    pub(crate) fn new(
        snapshot_id: SnapshotId,
        database: &'db Database<P>,
        lock: Option<RwLockReadGuard<'db, L>>,
    ) -> Self {
        Self {
            snapshot_id,
            committed: false,
            database,
            lock,
            _marker: std::marker::PhantomData,
        }
    }

    // pub fn get_storage_slot(&self, address_path: AddressPath, slot_key: StorageSlotKey) -> Result<StorageSlot, ()> {
    //     todo!()
    // }
}

impl<'db, P: PageManager, L> Transaction<'db, RW, P, L> {
    // pub fn set_account(&mut self, address_path: AddressPath, account: Account) -> Result<(), ()> {
    //     todo!()
    // }

    // pub fn set_storage_slot(&mut self, address_path: AddressPath, slot_key: StorageSlotKey, slot: StorageSlot) -> Result<(), ()> {
    //     todo!()
    // }

    pub fn commit(mut self) -> Result<(), ()> {
        let mut storage_engine = self.database.inner.storage_engine.write().unwrap();
        let mut transaction_manager = self.database.inner.transaction_manager.write().unwrap();
        storage_engine.commit(self.snapshot_id).unwrap();
        transaction_manager.remove_transaction(self.snapshot_id, true)?;

        self.committed = true;
        Ok(())
    }

    pub fn rollback(mut self) -> Result<(), ()> {
        let mut storage_engine = self.database.inner.storage_engine.write().unwrap();
        let mut transaction_manager = self.database.inner.transaction_manager.write().unwrap();
        storage_engine.rollback(self.snapshot_id).unwrap();
        transaction_manager.remove_transaction(self.snapshot_id, true)?;

        self.committed = false;
        Ok(())
    }
}

impl<'db, P: PageManager, L> Transaction<'db, RO, P, L> {
    pub fn commit(mut self) -> Result<(), ()> {
        let mut transaction_manager = self.database.inner.transaction_manager.write().unwrap();
        transaction_manager.remove_transaction(self.snapshot_id, false)?;

        self.committed = true;
        Ok(())
    }
}

impl<'db, K: TransactionKind, P: PageManager, L> Drop for Transaction<'db, K, P, L> {
    fn drop(&mut self) {
        // TODO: panic if the transaction is not committed
    }
}
