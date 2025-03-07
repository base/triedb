mod manager;

use std::{fmt::Debug, sync::RwLockReadGuard};

use crate::{
    account::Account,
    database::{Database, TransactionContext},
    page::PageManager,
    path::{AddressPath, StoragePath},
    storage::engine::StorageEngine,
};
use alloy_primitives::StorageValue;
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
    context: TransactionContext,
    database: &'tx Database<P>,
    _lock: Option<RwLockReadGuard<'tx, StorageEngine<P>>>,
    _marker: std::marker::PhantomData<K>,
}

impl<'tx, K: TransactionKind, P: PageManager> Transaction<'tx, K, P> {
    pub(crate) fn new(
        context: TransactionContext,
        database: &'tx Database<P>,
        _lock: Option<RwLockReadGuard<'tx, StorageEngine<P>>>,
    ) -> Self {
        Self {
            committed: false,
            context,
            database,
            _lock,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn get_account(&'tx self, address_path: AddressPath) -> Result<Option<Account>, ()> {
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        let account = storage_engine
            .get_account(&self.context, address_path)
            .unwrap();

        self.database.update_metrics_ro(&self.context);

        Ok(account)
    }

    pub fn get_storage_slot(&self, storage_path: StoragePath) -> Result<Option<StorageValue>, ()> {
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        let storage_slot = storage_engine
            .get_storage(&self.context, storage_path)
            .unwrap();
        Ok(storage_slot)
    }
}

impl<P: PageManager> Transaction<'_, RW, P> {
    pub fn set_account(
        &mut self,
        address_path: AddressPath,
        account: Option<Account>,
    ) -> Result<(), ()> {
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        storage_engine
            .set_account(&mut self.context, address_path, account)
            .unwrap();

        self.database.update_metrics_rw(&self.context);

        Ok(())
    }

    pub fn set_storage_slot(
        &mut self,
        storage_path: StoragePath,
        value: Option<StorageValue>,
    ) -> Result<(), ()> {
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        storage_engine
            .set_storage(&mut self.context, storage_path, value)
            .unwrap();
        Ok(())
    }

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

    #[cfg(feature = "benchmarking")]
    pub fn no_op_commit(mut self) -> Result<(), ()> {
        let mut transaction_manager = self.database.inner.transaction_manager.write().unwrap();
        transaction_manager.remove_transaction(self.context.metadata.snapshot_id, true)?;

        self.committed = false;
        Ok(())
    }
}

impl<P: PageManager> Transaction<'_, RO, P> {
    pub fn commit(mut self) -> Result<(), ()> {
        let mut transaction_manager = self.database.inner.transaction_manager.write().unwrap();
        transaction_manager.remove_transaction(self.context.metadata.snapshot_id, false)?;

        self.committed = true;
        Ok(())
    }
}

impl<K: TransactionKind, P: PageManager> Drop for Transaction<'_, K, P> {
    fn drop(&mut self) {
        // TODO: panic if the transaction is not committed
    }
}
