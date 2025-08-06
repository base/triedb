use alloy_primitives::{B256, U256};
use alloy_rlp::{MaxEncodedLen, RlpEncodable};
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use proptest::prelude::*;
use proptest_derive::Arbitrary;

#[derive(Debug, Clone, PartialEq, Eq, Default, Arbitrary, RlpEncodable)]
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

/// This is the maximum possible RLP-encoded length of an account.
///
/// This value is derived from the maximum possible length of an account, which is the largest
/// case. An account is encoded as a list of 4 elements, with 3 of these represnting 32 byte values
/// and the nonce being an 8 byte value. Each element has 1 extra byte of encoding overhead.
/// The list also has 2 bytes of encoding overhead. The total length is `2 + 3*33 + 9 = 110`.
const MAX_RLP_ENCODED_LEN: usize = 2 + 3*33 + 9;

unsafe impl MaxEncodedLen<MAX_RLP_ENCODED_LEN> for Account {}

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
