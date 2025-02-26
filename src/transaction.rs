mod manager;

use std::{fmt::Debug, sync::RwLockReadGuard};

use crate::{
    account::Account,
    database::{Database, Metadata, TransactionContext},
    page::PageManager,
    path::AddressPath,
    storage::{engine::StorageEngine, value::Value},
};
use alloy_rlp::Encodable;
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
pub struct Transaction<'tx, K: TransactionKind, P: PageManager> {
    committed: bool,
    // metadata: Metadata,
    context: TransactionContext,
    database: &'tx Database<P>,
    lock: Option<RwLockReadGuard<'tx, StorageEngine<P>>>,
    _marker: std::marker::PhantomData<K>,
}

impl<'tx, K: TransactionKind, P: PageManager> Transaction<'tx, K, P> {
    pub(crate) fn new(
        context: TransactionContext,
        database: &'tx Database<P>,
        lock: Option<RwLockReadGuard<'tx, StorageEngine<P>>>,
    ) -> Self {
        Self {
            committed: false,
            context,
            database,
            lock,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn get_account<A: Account + Value>(
        &'tx self,
        address_path: AddressPath,
    ) -> Result<Option<A>, ()> {
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        let account = storage_engine
            .get_account(&self.context, address_path)
            .unwrap();
        Ok(account)
    }

    // pub fn get_storage_slot(&self, address_path: AddressPath, slot_key: StorageSlotKey) -> Result<StorageSlot, ()> {
    //     todo!()
    // }
}

impl<'tx, P: PageManager> Transaction<'tx, RW, P> {
    pub fn set_account<A: Account + Value + Encodable + Clone>(
        &mut self,
        address_path: AddressPath,
        account: Option<A>,
    ) -> Result<(), ()> {
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        storage_engine
            .set_account(&mut self.context, address_path, account)
            .unwrap();
        Ok(())
    }

    // pub fn set_storage_slot(&mut self, address_path: AddressPath, slot_key: StorageSlotKey, slot: StorageSlot) -> Result<(), ()> {
    //     todo!()
    // }

    pub fn commit(mut self) -> Result<(), ()> {
        let mut transaction_manager = self.database.inner.transaction_manager.write().unwrap();
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        storage_engine.commit(&self.context).unwrap();
        let mut metadata = self.database.inner.metadata.write().unwrap();
        *metadata = self.context.metadata.clone();
        transaction_manager.remove_transaction(self.context.metadata.snapshot_id, true)?;

        self.committed = true;
        Ok(())
    }

    pub fn rollback(mut self) -> Result<(), ()> {
        let mut transaction_manager = self.database.inner.transaction_manager.write().unwrap();
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        storage_engine.rollback(&self.context).unwrap();
        transaction_manager.remove_transaction(self.context.metadata.snapshot_id, true)?;

        self.committed = false;
        Ok(())
    }
}

impl<'tx, P: PageManager> Transaction<'tx, RO, P> {
    pub fn commit(mut self) -> Result<(), ()> {
        let mut transaction_manager = self.database.inner.transaction_manager.write().unwrap();
        transaction_manager.remove_transaction(self.context.metadata.snapshot_id, false)?;

        self.committed = true;
        Ok(())
    }
}

impl<'tx, K: TransactionKind, P: PageManager> Drop for Transaction<'tx, K, P> {
    fn drop(&mut self) {
        // TODO: panic if the transaction is not committed
    }
}
