#![cfg(test)]

use crate::{
    account::Account, context::TransactionContext, executor::threadpool, meta::MetadataManager,
    storage::{engine::StorageEngine, proofs::{AccountProof, StorageProof}},
    PageManager,
};
use alloy_primitives::{B256, U256};
use alloy_rlp::encode;
use alloy_trie::{proof::verify_proof, TrieAccount, EMPTY_ROOT_HASH, KECCAK_EMPTY};
use rand::{rngs::StdRng, RngCore};

pub(crate) fn create_test_engine(max_pages: u32) -> (StorageEngine, TransactionContext) {
    let meta_manager =
        MetadataManager::from_file(tempfile::tempfile().expect("failed to create temporary file"))
            .expect("failed to open metadata file");
    let page_manager = PageManager::options()
        .max_pages(max_pages)
        .open_temp_file()
        .expect("failed to create page manager");
    let thread_pool = threadpool::builder().build().expect("failed to create thread pool");
    let storage_engine = StorageEngine::new(page_manager, meta_manager, thread_pool);
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

/// Verifies that an account proof is valid against the given root hash.
///
/// This function validates both the account proof itself and any included storage proofs.
/// It will panic with a descriptive message if verification fails.
pub(crate) fn verify_account_proof(proof: &AccountProof, root: B256) {
    let expected = Some(encode(TrieAccount {
        nonce: proof.account.nonce,
        balance: proof.account.balance,
        storage_root: proof.account.storage_root,
        code_hash: proof.account.code_hash,
    }));
    verify_proof(root, proof.hashed_address.clone(), expected, proof.proof.values())
        .expect("failed to verify account proof");

    // Verify all storage proofs against the account's storage root
    for storage_proof in proof.storage_proofs.values() {
        verify_storage_proof(storage_proof, proof.account.storage_root);
    }
}

/// Verifies that a storage proof is valid against the given storage root hash.
///
/// This function validates the storage proof, including handling zero values
/// (which are represented as None in the trie). It will panic with a descriptive
/// message if verification fails.
pub(crate) fn verify_storage_proof(proof: &StorageProof, root: B256) {
    let expected_value = if proof.value.is_zero() {
        None
    } else {
        Some(alloy_rlp::encode(proof.value))
    };
    verify_proof(
        root,
        proof.hashed_slot.clone(),
        expected_value,
        proof.proof.values(),
    )
    .expect("failed to verify storage proof");
}