use crate::page::PageId;
use alloy_primitives::{hex, StorageValue, B256, U256};
use alloy_rlp::{BufMut, Encodable, RlpEncodable};
use std::fmt::Debug;

use crate::storage::value::{self, Value, ValueRef};

pub trait Account {
    fn balance(&self) -> U256;
    fn nonce(&self) -> u64;
    fn code_hash(&self) -> B256;
    fn storage_root(&self) -> B256;
    fn storage_root_subtrie_page_id(&self) -> PageId;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccountVec {
    data: Vec<u8>,
}

impl AccountVec {
    pub fn new(
        balance: U256,
        nonce: u64,
        code_hash: B256,
        storage_root: B256,
        storage_root_subtrie_page_id: PageId,
    ) -> Self {
        let mut data = vec![0; 108];
        data[0..32].copy_from_slice(&balance.to_be_bytes::<32>());
        data[32..40].copy_from_slice(&nonce.to_be_bytes());
        data[40..72].copy_from_slice(&code_hash.as_slice());
        data[72..104].copy_from_slice(&storage_root.as_slice());
        data[104..108].copy_from_slice(&storage_root_subtrie_page_id.to_le_bytes());
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

    fn storage_root_subtrie_page_id(&self) -> PageId {
        PageId::from_le_bytes(self.data[104..108].try_into().expect("page_id is 4 bytes"))
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
        storage_root_subtrie_page_id: PageId,
        data: &'a mut [u8],
    ) -> Self {
        data[0..32].copy_from_slice(&balance.to_be_bytes::<32>());
        data[32..40].copy_from_slice(&nonce.to_be_bytes());
        data[40..72].copy_from_slice(&code_hash.as_slice());
        data[72..104].copy_from_slice(&storage_root.as_slice());
        data[104..108].copy_from_slice(&storage_root_subtrie_page_id.to_le_bytes());
        Self { data }
    }
}

impl<'a> Account for AccountSlice<'a> {
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
    fn storage_root_subtrie_page_id(&self) -> PageId {
        PageId::from_le_bytes(self.data[104..108].try_into().expect("page id is 4 bytes"))
    }
}

impl Value for AccountVec {
    fn to_bytes(self) -> Vec<u8> {
        self.data
    }

    fn from_bytes(bytes: &[u8]) -> value::Result<Self> {
        Ok(Self {
            data: bytes.to_vec(),
        })
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

impl Value for StorageValue {
    fn to_bytes(self) -> Vec<u8> {
        self.to_be_bytes::<32>().to_vec()
    }

    fn from_bytes(bytes: &[u8]) -> value::Result<Self> {
        Ok(Self::from_be_slice(bytes))
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
