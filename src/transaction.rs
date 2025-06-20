mod error;
mod manager;

use crate::{
    account::Account,
    context::TransactionContext,
    database::Database,
    node::TrieValue,
    path::{AddressPath, StoragePath}, storage::cursor::Cursor,
};
use alloy_primitives::{StorageValue, B256};
use alloy_trie::Nibbles;
pub use error::TransactionError;
pub use manager::TransactionManager;
use reth_trie_common::MultiProof;
use sealed::sealed;
use std::{collections::HashMap, fmt::Debug};

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
    consumer::<Transaction<'_, RO>>();
    consumer::<Transaction<'_, RW>>();
};

#[derive(Debug)]
pub struct Transaction<'tx, K: TransactionKind> {
    committed: bool,
    context: TransactionContext,
    database: &'tx Database,
    pending_changes: HashMap<Nibbles, Option<TrieValue>>,
    _marker: std::marker::PhantomData<K>,
}

impl<'tx, K: TransactionKind> Transaction<'tx, K> {
    pub(crate) fn new(context: TransactionContext, database: &'tx Database) -> Self {
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
        let account =
            self.database.storage_engine.get_account(&mut self.context, address_path).unwrap();
        self.database.update_metrics_ro(&self.context);
        Ok(account)
    }

    pub fn get_storage_slot(
        &mut self,
        storage_path: StoragePath,
    ) -> Result<Option<StorageValue>, TransactionError> {
        let storage_slot =
            self.database.storage_engine.get_storage(&mut self.context, storage_path).unwrap();
        self.database.update_metrics_ro(&self.context);
        Ok(storage_slot)
    }

    pub fn state_root(&self) -> B256 {
        self.context.root_node_hash
    }

    pub fn get_account_with_proof(
        &self,
        address_path: AddressPath,
    ) -> Result<Option<(Account, MultiProof)>, TransactionError> {
        let result = self
            .database
            .storage_engine
            .get_account_with_proof(&self.context, address_path)
            .unwrap();
        Ok(result)
    }

    pub fn get_storage_with_proof(
        &self,
        storage_path: StoragePath,
    ) -> Result<Option<(StorageValue, MultiProof)>, TransactionError> {
        let result = self
            .database
            .storage_engine
            .get_storage_with_proof(&self.context, storage_path)
            .unwrap();
        Ok(result)
    }

    pub fn debug_account(
        &self,
        output_file: impl std::io::Write,
        address_path: AddressPath,
        verbosity_level: u8,
    ) -> Result<(), TransactionError> {
        self.database
            .storage_engine
            .print_path(&self.context, address_path.to_nibbles(), output_file, verbosity_level)
            .unwrap();
        Ok(())
    }

    pub fn debug_storage(
        &self,
        output_file: Box<dyn std::io::Write>,
        storage_path: StoragePath,
        verbosity_level: u8,
    ) -> Result<(), TransactionError> {
        self.database
            .storage_engine
            .print_path(&self.context, &storage_path.full_path(), output_file, verbosity_level)
            .unwrap();
        Ok(())
    }

    pub fn new_account_cursor(&self) -> Cursor {
        Cursor::new_account_cursor(&self.database.storage_engine, &self.context)
    }

    pub fn new_storage_cursor(&self, address_path: AddressPath) -> Cursor {
        Cursor::new_storage_cursor(&self.database.storage_engine, &self.context, address_path.into())
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
        let mut changes =
            self.pending_changes.drain().collect::<Vec<(Nibbles, Option<TrieValue>)>>();

        if !changes.is_empty() {
            self.database.storage_engine.set_values(&mut self.context, changes.as_mut()).unwrap();
        }

        let mut transaction_manager = self.database.transaction_manager.lock();
        self.database.storage_engine.commit(&self.context).unwrap();

        self.database.update_metrics_rw(&self.context);

        transaction_manager.remove_tx(self.context.snapshot_id, true);

        self.committed = true;
        Ok(())
    }

    pub fn rollback(mut self) -> Result<(), TransactionError> {
        self.database.storage_engine.rollback(&self.context).unwrap();

        let mut transaction_manager = self.database.transaction_manager.lock();
        transaction_manager.remove_tx(self.context.snapshot_id, true);

        self.committed = false;
        Ok(())
    }
}

impl Transaction<'_, RO> {
    pub fn commit(mut self) -> Result<(), TransactionError> {
        let mut transaction_manager = self.database.transaction_manager.lock();
        transaction_manager.remove_tx(self.context.snapshot_id, false);

        self.committed = true;
        Ok(())
    }
}

impl<K: TransactionKind> Drop for Transaction<'_, K> {
    fn drop(&mut self) {
        // TODO: panic if the transaction is not committed
    }
}
