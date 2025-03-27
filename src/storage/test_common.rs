use alloy_trie::EMPTY_ROOT_HASH;

use crate::{
    context::TransactionContext, database::Metadata, page::OrphanPageManager, MmapPageManager,
};

use crate::account::Account;
use alloy_primitives::{address, b256, hex, keccak256, Address, StorageKey, B256, U256};
use alloy_trie::{
    root::{storage_root_unhashed, storage_root_unsorted},
    EMPTY_ROOT_HASH, KECCAK_EMPTY,
};
use proptest::prelude::*;
use rand::{rngs::StdRng, RngCore};

use super::engine::StorageEngine;

#[cfg(test)]
pub fn create_test_engine(page_count: u32) -> (StorageEngine<MmapPageManager>, TransactionContext) {
    let manager = MmapPageManager::new_anon(page_count, 256).unwrap();
    let orphan_manager = OrphanPageManager::new();
    let metadata = Metadata {
        snapshot_id: 1,
        root_page_id: 0,
        max_page_number: 255,
        root_subtrie_page_id: 0,
        state_root: EMPTY_ROOT_HASH,
    };
    let storage_engine = StorageEngine::new(manager, orphan_manager);
    (storage_engine, TransactionContext::new(metadata))
}

#[cfg(test)]
pub fn random_test_account(rng: &mut StdRng) -> Account {
    create_test_account(rng.next_u64(), rng.next_u64())
}

#[cfg(test)]
pub fn create_test_account(balance: u64, nonce: u64) -> Account {
    Account::new(nonce, U256::from(balance), EMPTY_ROOT_HASH, KECCAK_EMPTY)
}
