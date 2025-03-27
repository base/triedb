#[cfg(test)]
pub mod test_common {
    use crate::{
        account::Account, context::TransactionContext, database::Metadata, page::OrphanPageManager,
        storage::engine::StorageEngine, MmapPageManager,
    };
    use alloy_primitives::U256;
    use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
    use rand::{rngs::StdRng, RngCore};

    pub fn create_test_engine(
        page_count: u32,
    ) -> (StorageEngine<MmapPageManager>, TransactionContext) {
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

    pub fn random_test_account(rng: &mut StdRng) -> Account {
        create_test_account(rng.next_u64(), rng.next_u64())
    }

    pub fn create_test_account(balance: u64, nonce: u64) -> Account {
        Account::new(nonce, U256::from(balance), EMPTY_ROOT_HASH, KECCAK_EMPTY)
    }
}
