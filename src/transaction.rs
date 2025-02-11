mod manager;

use std::fmt::Debug;

use crate::{
    database::Database,
    page::{PageId, PageManager, ReadablePage},
    snapshot::SnapshotId,
};
pub use manager::TransactionManager;

pub trait TransactionKind: Debug {
    fn sealed() -> ();
}

#[derive(Debug)]
pub struct RW {}

impl TransactionKind for RW {
    fn sealed() -> () {
        ()
    }
}

#[derive(Debug)]
pub struct RO {}

impl TransactionKind for RO {
    fn sealed() -> () {
        ()
    }
}

#[derive(Debug)]
pub struct Transaction<'db, K: TransactionKind, P: PageManager> {
    snapshot_id: SnapshotId,
    committed: bool,
    database: &'db Database<P>,
    _marker: std::marker::PhantomData<K>,
}

impl<'db, K: TransactionKind, P: PageManager> Transaction<'db, K, P> {
    pub(crate) fn new(snapshot_id: SnapshotId, database: &'db Database<P>) -> Self {
        Self {
            snapshot_id,
            committed: false,
            database,
            _marker: std::marker::PhantomData,
        }
    }

    // pub fn get_account(&self, address_path: AddressPath) -> Result<Account, ()> {
    //     todo!()
    // }

    // pub fn get_storage_slot(&self, address_path: AddressPath, slot_key: StorageSlotKey) -> Result<StorageSlot, ()> {
    //     todo!()
    // }
}

impl<'db, P: PageManager> Transaction<'db, RW, P> {
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

impl<'db, P: PageManager> Transaction<'db, RO, P> {
    pub fn commit(mut self) -> Result<(), ()> {
        let mut transaction_manager = self.database.inner.transaction_manager.write().unwrap();
        transaction_manager.remove_transaction(self.snapshot_id, false)?;

        self.committed = true;
        Ok(())
    }
}

impl<'db, K: TransactionKind, P: PageManager> Drop for Transaction<'db, K, P> {
    fn drop(&mut self) {
        // TODO: panic if the transaction is not committed
    }
}
