mod error;
mod manager;

use crate::{
    account::Account,
    context::TransactionContext,
    database::Database,
    node::TrieValue,
    path::{AddressPath, StoragePath},
};
use alloy_primitives::{StorageValue, B256};
use alloy_trie::Nibbles;
pub use error::TransactionError;
pub use manager::TransactionManager;
use reth_trie_common::MultiProof;
use sealed::sealed;
use std::{collections::HashMap, fmt::Debug, sync::Arc};

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

// Compile-time assertion to ensure that `Transaction` is `Send`
const _: fn() = || {
    fn consumer<T: Send>() {}
    consumer::<Transaction<RO>>();
    consumer::<Transaction<RW>>();
};

#[derive(Debug)]
pub struct Transaction<K: TransactionKind> {
    committed: bool,
    context: TransactionContext,
    database: Arc<Database>,
    pending_changes: HashMap<Nibbles, Option<TrieValue>>,
    _marker: std::marker::PhantomData<K>,
}

impl<K: TransactionKind> Transaction<K> {
    pub(crate) fn new(context: TransactionContext, database: Arc<Database>) -> Self {
        Self {
            committed: false,
            context,
            database,
            pending_changes: HashMap::new(),
            _marker: std::marker::PhantomData,
        }
    }

    pub fn get_account(
        &mut self,
        address_path: AddressPath,
    ) -> Result<Option<Account>, TransactionError> {
        let storage_engine = self.database.inner.storage_engine.read();
        let account = storage_engine.get_account(&mut self.context, address_path).unwrap();

        self.database.update_metrics_ro(&self.context);

        Ok(account)
    }

    pub fn get_storage_slot(
        &mut self,
        storage_path: StoragePath,
    ) -> Result<Option<StorageValue>, TransactionError> {
        let storage_engine = self.database.inner.storage_engine.read();
        let storage_slot = storage_engine.get_storage(&mut self.context, storage_path).unwrap();

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
        let storage_engine = self.database.inner.storage_engine.read();
        let result = storage_engine.get_account_with_proof(&self.context, address_path).unwrap();
        Ok(result)
    }

    pub fn get_storage_with_proof(
        &self,
        storage_path: StoragePath,
    ) -> Result<Option<(StorageValue, MultiProof)>, TransactionError> {
        let storage_engine = self.database.inner.storage_engine.read();
        let result = storage_engine.get_storage_with_proof(&self.context, storage_path).unwrap();
        Ok(result)
    }

    pub fn debug_account(
        &self,
        output_file: &std::fs::File,
        address_path: AddressPath,
        verbosity_level: u32,
    ) -> Result<(), TransactionError> {
        let context = self.context.clone();
        let storage_engine = self.database.inner.storage_engine.read();

        storage_engine
            .print_path(&context, address_path.to_nibbles(), output_file, verbosity_level)
            .unwrap();
        Ok(())
    }

    pub fn debug_storage(
        &self,
        output_file: &std::fs::File,
        storage_path: StoragePath,
        verbosity_level: u32,
    ) -> Result<(), TransactionError> {
        let context = self.context.clone();
        let storage_engine = self.database.inner.storage_engine.read();

        storage_engine
            .print_path(&context, &storage_path.full_path(), output_file, verbosity_level)
            .unwrap();
        Ok(())
    }
}

impl Transaction<RW> {
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

    pub fn commit(&mut self) -> Result<(), TransactionError> {
        let mut storage_engine = self.database.inner.storage_engine.write();
        let mut changes =
            self.pending_changes.drain().collect::<Vec<(Nibbles, Option<TrieValue>)>>();

        if !changes.is_empty() {
            storage_engine.set_values(&mut self.context, changes.as_mut()).unwrap();
        }

        let mut transaction_manager = self.database.inner.transaction_manager.write();
        storage_engine.commit(&self.context).unwrap();

        let mut metadata = self.database.inner.metadata.write();
        *metadata = self.context.metadata.clone();

        self.database.update_metrics_rw(&self.context);

        transaction_manager.remove_transaction(self.context.metadata.snapshot_id, true)?;

        self.committed = true;
        Ok(())
    }

    pub fn rollback(mut self) -> Result<(), TransactionError> {
        let mut transaction_manager = self.database.inner.transaction_manager.write();
        let storage_engine = self.database.inner.storage_engine.read();
        // TODO: this is temperorary until we actually implement rollback.
        // we need to update the metadata to the next snapshot id.
        let mut metadata = self.database.inner.metadata.write();
        *metadata = self.context.metadata.clone();

        storage_engine.rollback(&self.context).unwrap();
        transaction_manager.remove_transaction(self.context.metadata.snapshot_id, true)?;

        self.committed = false;
        Ok(())
    }
}

impl Transaction<RO> {
    pub fn commit(mut self) -> Result<(), TransactionError> {
        let mut transaction_manager = self.database.inner.transaction_manager.write();
        transaction_manager.remove_transaction(self.context.metadata.snapshot_id, false)?;

        self.committed = true;
        Ok(())
    }
}

impl<K: TransactionKind> Drop for Transaction<K> {
    fn drop(&mut self) {
        // TODO: panic if the transaction is not committed
    }
}
