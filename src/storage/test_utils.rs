#![cfg(test)]

use alloy_primitives::U256;
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use rand::{rngs::StdRng, RngCore};

use crate::{
    account::Account, context::TransactionContext, database::Metadata, page::OrphanPageManager,
    storage::engine::StorageEngine, PageManager,
};

pub(crate) fn create_test_engine(max_pages: u32) -> (StorageEngine, TransactionContext) {
    let mut page_manager = PageManager::options().max_pages(max_pages).open_temp_file().unwrap();
    for _ in 0..256 {
        page_manager.allocate(0).unwrap();
    }

    let orphan_manager = OrphanPageManager::new();
    let metadata = Metadata {
        snapshot_id: 1,
        root_page_id: 0,
        max_page_number: 255,
        root_subtrie_page_id: 0,
        state_root: EMPTY_ROOT_HASH,
    };
    let storage_engine = StorageEngine::new(page_manager, orphan_manager);

    (storage_engine, TransactionContext::new(metadata))
}

pub(crate) fn random_test_account(rng: &mut StdRng) -> Account {
    create_test_account(rng.next_u64(), rng.next_u64())
}

pub(crate) fn create_test_account(balance: u64, nonce: u64) -> Account {
    Account::new(nonce, U256::from(balance), EMPTY_ROOT_HASH, KECCAK_EMPTY)
}

pub(crate) fn assert_metrics(
    context: &TransactionContext,
    pages_read: u32,
    pages_allocated: u32,
    pages_reallocated: u32,
    pages_split: u32,
) {
    assert_eq!(
        context.transaction_metrics.get_pages_read(),
        pages_read,
        "unexpected number of pages read"
    );
    assert_eq!(
        context.transaction_metrics.get_pages_allocated(),
        pages_allocated,
        "unexpected number of pages allocated"
    );
    assert_eq!(
        context.transaction_metrics.get_pages_reallocated(),
        pages_reallocated,
        "unexpected number of pages reallocated"
    );
    assert_eq!(
        context.transaction_metrics.get_pages_split(),
        pages_split,
        "unexpected number of pages split"
    );
}
