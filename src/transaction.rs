mod error;
mod manager;

use std::{fmt::Debug, sync::RwLockReadGuard};

use crate::{
    account::Account,
    context::TransactionContext,
    database::Database,
    node::TrieValue,
    path::{AddressPath, StoragePath},
    storage::engine::StorageEngine,
};
use alloy_primitives::{StorageValue, B256};
use alloy_trie::Nibbles;
pub use error::TransactionError;
pub use manager::TransactionManager;
use reth_trie_common::MultiProof;
use sealed::sealed;
use std::collections::HashMap;

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
pub struct Transaction<'tx, K: TransactionKind> {
    committed: bool,
    context: TransactionContext,
    database: &'tx Database,
    pending_changes: HashMap<Nibbles, Option<TrieValue>>,
    _lock: Option<RwLockReadGuard<'tx, StorageEngine>>,
    _marker: std::marker::PhantomData<K>,
}

impl<'tx, K: TransactionKind> Transaction<'tx, K> {
    pub(crate) fn new(
        context: TransactionContext,
        database: &'tx Database,
        lock: Option<RwLockReadGuard<'tx, StorageEngine>>,
    ) -> Self {
        Self {
            committed: false,
            context,
            database,
            pending_changes: HashMap::new(),
            _lock: lock,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn get_account(
        &'tx self,
        address_path: AddressPath,
    ) -> Result<Option<Account>, TransactionError> {
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        let account = storage_engine.get_account(&self.context, address_path).unwrap();

        self.database.update_metrics_ro(&self.context);

        Ok(account)
    }

    pub fn get_storage_slot(
        &self,
        storage_path: StoragePath,
    ) -> Result<Option<StorageValue>, TransactionError> {
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        let storage_slot = storage_engine.get_storage(&self.context, storage_path).unwrap();

        self.database.update_metrics_ro(&self.context);
        Ok(storage_slot)
    }

    pub fn state_root(&self) -> B256 {
        self.context.metadata.state_root
    }

    pub fn get_account_with_proof(
        &self,
        address_path: AddressPath,
    ) -> Result<Option<(Account, MultiProof)>, TransactionError> {
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        let result = storage_engine.get_account_with_proof(&self.context, address_path).unwrap();
        Ok(result)
    }

    pub fn get_storage_with_proof(
        &self,
        storage_path: StoragePath,
    ) -> Result<Option<(StorageValue, MultiProof)>, TransactionError> {
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        let result = storage_engine.get_storage_with_proof(&self.context, storage_path).unwrap();
        Ok(result)
    }
}

impl Transaction<'_, RW> {
    pub fn set_account(
        &mut self,
        address_path: AddressPath,
        account: Option<Account>,
    ) -> Result<(), TransactionError> {
        self.pending_changes.insert(address_path.into(), account.map(TrieValue::Account));
        Ok(())
    }

    pub fn set_storage_slot(
        &mut self,
        storage_path: StoragePath,
        value: Option<StorageValue>,
    ) -> Result<(), TransactionError> {
        self.pending_changes.insert(storage_path.full_path(), value.map(TrieValue::Storage));
        Ok(())
    }

    pub fn commit(mut self) -> Result<(), TransactionError> {
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        let mut changes =
            self.pending_changes.drain().collect::<Vec<(Nibbles, Option<TrieValue>)>>();

        if !changes.is_empty() {
            // Assume the worst case scenario where each account and storage slot requires a new
            // page, plus an extra buffer TODO: page buffer and grow_by should be
            // configurable, but for now 1000 is assumed to be good enough.
            // It's also possible that we could use a more sophisticated algorithm to estimate the
            // number of pages required. Note that resizing the current memory-mapped
            // page manager requires remapping all pages, and cannot be done while any readers are
            // open.
            storage_engine
                .ensure_page_buffer(&self.context, changes.len() as u32 + 1000, 1.2)
                .unwrap();

            storage_engine.set_values(&mut self.context, changes.as_mut()).unwrap();
        }

        let mut transaction_manager = self.database.inner.transaction_manager.write().unwrap();
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        storage_engine.commit(&self.context).unwrap();

        let mut metadata = self.database.inner.metadata.write().unwrap();
        *metadata = self.context.metadata.clone();

        self.database.update_metrics_rw(&self.context);

        transaction_manager.remove_transaction(self.context.metadata.snapshot_id, true)?;

        self.committed = true;
        Ok(())
    }

    pub fn rollback(mut self) -> Result<(), TransactionError> {
        let mut transaction_manager = self.database.inner.transaction_manager.write().unwrap();
        let storage_engine = self.database.inner.storage_engine.read().unwrap();
        // TODO: this is temperorary until we actually implement rollback.
        // we need to update the metadata to the next snapshot id.
        let mut metadata = self.database.inner.metadata.write().unwrap();
        *metadata = self.context.metadata.clone();

        storage_engine.rollback(&self.context).unwrap();
        transaction_manager.remove_transaction(self.context.metadata.snapshot_id, true)?;

        self.committed = false;
        Ok(())
    }
}

impl Transaction<'_, RO> {
    pub fn commit(mut self) -> Result<(), TransactionError> {
        let mut transaction_manager = self.database.inner.transaction_manager.write().unwrap();
        transaction_manager.remove_transaction(self.context.metadata.snapshot_id, false)?;

        self.committed = true;
        Ok(())
    }
}

impl<K: TransactionKind> Drop for Transaction<'_, K> {
    fn drop(&mut self) {
        // TODO: panic if the transaction is not committed
    }
}
