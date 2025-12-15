mod error;
mod manager;

use crate::{
    account::Account,
    context::TransactionContext,
    database::Database,
    node::TrieValue,
    overlay::OverlayState,
    path::{AddressPath, RawPath, StoragePath},
    storage::{overlay_root::OverlayedRoot, proofs::AccountProof},
};
use alloy_primitives::{map::HashMap, StorageValue, B256};
pub use error::TransactionError;
pub use manager::TransactionManager;
use sealed::sealed;
use std::{fmt::Debug, ops::Deref, sync::Arc};

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
    consumer::<Transaction<&Database, RO>>();
    consumer::<Transaction<&Database, RW>>();
    consumer::<Transaction<Arc<Database>, RO>>();
    consumer::<Transaction<Arc<Database>, RW>>();
};

#[derive(Debug)]
pub struct Transaction<DB, K: TransactionKind> {
    committed: bool,
    context: TransactionContext,
    database: DB,
    pending_changes: HashMap<RawPath, Option<TrieValue>>,
    _marker: std::marker::PhantomData<K>,
}

impl<DB: Deref<Target = Database>, K: TransactionKind> Transaction<DB, K> {
    pub(crate) fn new(context: TransactionContext, database: DB) -> Self {
        Self {
            committed: false,
            context,
            database,
            pending_changes: HashMap::default(),
            _marker: std::marker::PhantomData,
        }
    }

    pub fn get_account(
        &mut self,
        address_path: &AddressPath,
    ) -> Result<Option<Account>, TransactionError> {
        let account =
            self.database.storage_engine.get_account(&mut self.context, address_path).unwrap();
        self.database.update_metrics_ro(&self.context);
        Ok(account)
    }

    pub fn get_storage_slot(
        &mut self,
        storage_path: &StoragePath,
    ) -> Result<Option<StorageValue>, TransactionError> {
        let storage_slot =
            self.database.storage_engine.get_storage(&mut self.context, storage_path).unwrap();
        self.database.update_metrics_ro(&self.context);
        Ok(storage_slot)
    }

    pub fn state_root(&self) -> B256 {
        self.context.root_node_hash
    }

    pub fn compute_root_with_overlay(
        &self,
        overlay_state: OverlayState,
    ) -> Result<OverlayedRoot, TransactionError> {
        self.database
            .storage_engine
            .compute_state_root_with_overlay(&self.context, overlay_state)
            .map_err(|_| TransactionError)
    }

    pub fn get_account_with_proof(
        &self,
        address_path: AddressPath,
    ) -> Result<Option<AccountProof>, TransactionError> {
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
    ) -> Result<Option<AccountProof>, TransactionError> {
        let result = self
            .database
            .storage_engine
            .get_storage_with_proof(&self.context, storage_path)
            .unwrap();
        Ok(result)
    }

    pub fn clear_cache(&mut self) {
        self.context.clear_cache();
    }

    pub fn debug_account(
        &self,
        output_file: impl std::io::Write,
        address_path: AddressPath,
        verbosity_level: u8,
    ) -> Result<(), TransactionError> {
        self.database
            .storage_engine
            .debugger()
            .print_path(&self.context, &address_path.into(), output_file, verbosity_level)
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
            .debugger()
            .print_path(&self.context, &storage_path.into(), output_file, verbosity_level)
            .unwrap();
        Ok(())
    }
}

impl<DB: Deref<Target = Database>> Transaction<DB, RW> {
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
        self.pending_changes.insert(storage_path.into(), value.map(TrieValue::Storage));
        Ok(())
    }

    /// Applies changes to the trie using the standard sequential approach.
    pub fn set_values(
        &mut self,
        changes: &mut [(RawPath, Option<TrieValue>)],
    ) -> Result<(), TransactionError> {
        self.database
            .storage_engine
            .set_values_serial(&mut self.context, changes)
            .map_err(|_| TransactionError)
    }

    /// Same as set_values but with timing output for profiling.
    pub fn set_values_timed(
        &mut self,
        changes: &mut [(RawPath, Option<TrieValue>)],
        print_timing: bool,
    ) -> Result<(), TransactionError> {
        self.database
            .storage_engine
            .set_values_serial_timed(&mut self.context, changes, print_timing)
            .map_err(|_| TransactionError)
    }

    /// Applies changes to the trie using parallel hash computation.
    ///
    /// For large batches (>1000 changes), this may provide better performance
    /// by computing hashes in parallel using Rayon.
    pub fn set_values_parallel(
        &mut self,
        changes: &mut [(RawPath, Option<TrieValue>)],
    ) -> Result<(), TransactionError> {
        self.database
            .storage_engine
            .set_values(&mut self.context, changes)
            .map_err(|_| TransactionError)
    }

    /// Same as set_values_parallel but with timing output for profiling.
    pub fn set_values_parallel_timed(
        &mut self,
        changes: &mut [(RawPath, Option<TrieValue>)],
        print_timing: bool,
    ) -> Result<(), TransactionError> {
        self.database
            .storage_engine
            .set_values_parallel_timed(&mut self.context, changes, print_timing)
            .map_err(|_| TransactionError)
    }

    /// Applies changes to the trie using parallel subtree processing (V2).
    ///
    /// This is a new parallel approach that:
    /// 1. Processes same-page changes first (handles page splits)
    /// 2. Spawns parallel tasks for cross-page children
    /// 3. Computes hashes inline during traversal
    ///
    /// For batches with >1000 changes, this should provide significant speedup.
    /// For smaller batches, falls back to serial processing.
    pub fn set_values_parallel_v2(
        &mut self,
        changes: &mut [(RawPath, Option<TrieValue>)],
    ) -> Result<(), TransactionError> {
        self.database
            .storage_engine
            .set_values_parallel_v2(&mut self.context, changes)
            .map_err(|_| TransactionError)
    }

    pub fn commit(mut self) -> Result<(), TransactionError> {
        let mut changes = self.pending_changes.drain().collect::<Vec<_>>();
        if !changes.is_empty() {
            self.database
                .storage_engine
                .set_values_parallel_v2(&mut self.context, changes.as_mut())
                .unwrap();
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

impl<DB: Deref<Target = Database>> Transaction<DB, RO> {
    pub fn commit(mut self) -> Result<(), TransactionError> {
        let mut transaction_manager = self.database.transaction_manager.lock();
        transaction_manager.remove_tx(self.context.snapshot_id, false);

        self.committed = true;
        Ok(())
    }
}

impl<DB, K: TransactionKind> Drop for Transaction<DB, K> {
    fn drop(&mut self) {
        // TODO: panic if the transaction is not committed
    }
}
