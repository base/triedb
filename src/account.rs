use alloy_primitives::{B256, U256};
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use proptest::prelude::*;
use proptest_derive::Arbitrary;

#[derive(Debug, Clone, PartialEq, Eq, Default, Arbitrary)]
pub struct Account {
    pub nonce: u64,
    pub balance: U256,
    #[proptest(strategy = "prop_oneof!(any::<B256>(), Just(EMPTY_ROOT_HASH))")]
    pub storage_root: B256,
    #[proptest(strategy = "prop_oneof!(any::<B256>(), Just(KECCAK_EMPTY))")]
    pub code_hash: B256,
}

impl Account {
    pub fn new(nonce: u64, balance: U256, storage_root: B256, code_hash: B256) -> Self {
        Self { nonce, balance, storage_root, code_hash }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    proptest! {
        #[test]
        fn fuzz_account_fields(balance: U256, nonce: u64, code_hash: B256, storage_root: B256) {
            let account = Account::new(nonce, balance, storage_root, code_hash);
            assert_eq!(account.nonce, nonce);
            assert_eq!(account.balance, balance);
            assert_eq!(account.storage_root, storage_root);
            assert_eq!(account.code_hash, code_hash);
        }
    }
}
