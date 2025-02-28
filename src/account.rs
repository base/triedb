use alloy_primitives::{StorageValue, B256, U256};
use alloy_rlp::{BufMut, Encodable, RlpEncodable};
use proptest::{
    arbitrary::{Arbitrary, Mapped},
    prelude::{any, Strategy},
};
use std::fmt::Debug;

use crate::storage::value::{self, Value, ValueRef};

pub trait Account {
    fn balance(&self) -> U256;
    fn nonce(&self) -> u64;
    fn code_hash(&self) -> B256;
    fn storage_root(&self) -> B256;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccountVec {
    data: Vec<u8>,
}

impl AccountVec {
    pub fn new(balance: U256, nonce: u64, code_hash: B256, storage_root: B256) -> Self {
        let mut data = vec![0; 104];
        data[0..32].copy_from_slice(&balance.to_be_bytes::<32>());
        data[32..40].copy_from_slice(&nonce.to_be_bytes());
        data[40..72].copy_from_slice(code_hash.as_slice());
        data[72..104].copy_from_slice(storage_root.as_slice());
        Self { data }
    }
}

impl Account for AccountVec {
    fn balance(&self) -> U256 {
        U256::from_be_slice(&self.data[0..32])
    }

    fn nonce(&self) -> u64 {
        u64::from_be_bytes(self.data[32..40].try_into().expect("nonce is 8 bytes"))
    }

    fn code_hash(&self) -> B256 {
        B256::from_slice(&self.data[40..72])
    }

    fn storage_root(&self) -> B256 {
        B256::from_slice(&self.data[72..104])
    }
}

impl Value for AccountVec {
    fn to_bytes(&self) -> Vec<u8> {
        self.data.clone()
    }

    fn from_bytes(bytes: &[u8]) -> value::Result<Self> {
        Ok(Self {
            data: bytes.to_vec(),
        })
    }
}

#[derive(RlpEncodable, Debug)]
struct RlpAccount {
    nonce: u64,
    balance: U256,
    storage_root: B256,
    code_hash: B256,
}

impl Encodable for AccountVec {
    fn encode(&self, out: &mut dyn BufMut) {
        let rlp_account = RlpAccount {
            nonce: self.nonce(),
            balance: self.balance(),
            storage_root: self.storage_root(),
            code_hash: self.code_hash(),
        };
        rlp_account.encode(out);
    }
}

impl Arbitrary for AccountVec {
    type Parameters = ();
    type Strategy = Mapped<(U256, u64, B256, B256), AccountVec>;
    fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
        any::<(U256, u64, B256, B256)>().prop_map(
            move |(balance, nonce, code_hash, storage_root)| {
                AccountVec::new(balance, nonce, code_hash, storage_root)
            },
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccountSlice<'a> {
    data: &'a [u8],
}

impl<'a> AccountSlice<'a> {
    pub fn new(
        balance: U256,
        nonce: u64,
        code_hash: B256,
        storage_root: B256,
        data: &'a mut [u8],
    ) -> Self {
        data[0..32].copy_from_slice(&balance.to_be_bytes::<32>());
        data[32..40].copy_from_slice(&nonce.to_be_bytes());
        data[40..72].copy_from_slice(code_hash.as_slice());
        data[72..104].copy_from_slice(storage_root.as_slice());
        Self { data }
    }
}

impl Account for AccountSlice<'_> {
    fn balance(&self) -> U256 {
        U256::from_be_slice(&self.data[0..32])
    }

    fn nonce(&self) -> u64 {
        u64::from_be_bytes(self.data[32..40].try_into().expect("nonce is 8 bytes"))
    }

    fn code_hash(&self) -> B256 {
        B256::from_slice(&self.data[40..72])
    }

    fn storage_root(&self) -> B256 {
        B256::from_slice(&self.data[72..104])
    }
}

impl<'a> ValueRef<'a> for AccountSlice<'a> {
    type Owned = AccountVec;

    fn to_bytes(self) -> &'a [u8] {
        self.data
    }

    fn from_bytes(bytes: &'a [u8]) -> value::Result<Self> {
        Ok(Self { data: bytes })
    }

    fn to_owned(self) -> Self::Owned {
        AccountVec {
            data: self.data.to_vec(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum TrieValue {
    Storage(StorageValue),
    Account(AccountVec),
}

impl Value for TrieValue {
    fn to_bytes(&self) -> Vec<u8> {
        match self {
            Self::Storage(storage_value) => storage_value.to_be_bytes::<32>().to_vec(),
            Self::Account(account_vec) => account_vec.to_bytes(),
        }
    }

    fn from_bytes(bytes: &[u8]) -> value::Result<Self> {
        if bytes.len() == 32 {
            return Ok(Self::Storage(StorageValue::from_be_bytes::<32>(
                bytes.try_into().expect("storage value should be 32 bytes"),
            )));
        }

        Ok(Self::Account(AccountVec::from_bytes(bytes)?))
    }
}

impl Encodable for TrieValue {
    fn encode(&self, out: &mut dyn BufMut) {
        match self {
            Self::Storage(storage_value) => storage_value.encode(out),
            Self::Account(account_vec) => account_vec.encode(out),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn fuzz_account_fields(balance: U256, nonce: u64, code_hash: B256, storage_root: B256) {
            let account = AccountVec::new(balance, nonce, code_hash, storage_root);
            assert_eq!(account.balance(), balance);
            assert_eq!(account.nonce(), nonce);
            assert_eq!(account.code_hash(), code_hash);
            assert_eq!(account.storage_root(), storage_root);
        }

        #[test]
        fn fuzz_account_to_from_bytes(account: AccountVec) {
            let bytes = account.clone().to_bytes();
            let decoded = AccountVec::from_bytes(&bytes).unwrap();
            assert_eq!(account, decoded);
        }

        #[test]
        fn fuzz_account_rlp_encode(account: AccountVec) {
            let mut buf = vec![];
            account.encode(&mut buf);
        }
    }
}
