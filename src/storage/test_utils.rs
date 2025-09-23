#![cfg(test)]

use alloy_primitives::U256;
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use rand::{rngs::StdRng, RngCore};

use crate::{
    account::Account, context::TransactionContext, meta::MetadataManager,
    storage::engine::StorageEngine, PageManager,
};

pub(crate) fn create_test_engine(max_pages: u32) -> (StorageEngine, TransactionContext) {
    let meta_manager =
        MetadataManager::from_file(tempfile::tempfile().expect("failed to create temporary file"))
            .expect("failed to open metadata file");
    let page_manager = PageManager::options().max_pages(max_pages).open_temp_file().unwrap();
    let storage_engine = StorageEngine::new(page_manager, meta_manager);
    let context = storage_engine.write_context();
    (storage_engine, context)
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
    /// Struct used to make error messages easier to read
    #[derive(PartialEq, Eq, Debug)]
    struct Metrics {
        pages_read: u32,
        pages_allocated: u32,
        pages_reallocated: u32,
        pages_split: u32,
    }

    let expected = Metrics { pages_read, pages_allocated, pages_reallocated, pages_split };

    let actual = Metrics {
        pages_read: context.transaction_metrics.get_pages_read(),
        pages_allocated: context.transaction_metrics.get_pages_allocated(),
        pages_reallocated: context.transaction_metrics.get_pages_reallocated(),
        pages_split: context.transaction_metrics.get_pages_split(),
    };

    assert!(
        expected == actual,
        "transaction metrics don't match:\n expected: {expected:?}\n   actual: {actual:?}"
    );
}
