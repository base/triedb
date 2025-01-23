use std::fmt::Debug;

use alloy_primitives::B256;
use alloy_rlp::{Encodable, RlpEncodable};

pub trait Value: Debug + Clone + Default {
    fn as_bytes(&self) -> Vec<u8>;
    fn from_bytes(data: &[u8]) -> Self;
    fn rlp_encode(&self) -> Vec<u8>;
    // TODO: add method for RLP encoding
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StringValue(String);

impl Value for StringValue {
    fn as_bytes(&self) -> Vec<u8> {
        self.0.as_bytes().to_vec()
    }

    fn from_bytes(data: &[u8]) -> Self {
        let value = String::from_utf8(data.to_vec()).unwrap();
        Self(value)
    }

    fn rlp_encode(&self) -> Vec<u8> {
        alloy_rlp::encode(&self.0)
    }
}

impl From<String> for StringValue {
    fn from(value: String) -> Self {
        // left-pad the string to 32 bytes
        let mut data = vec![0u8; 32];
        data[32 - value.len()..].copy_from_slice(value.as_bytes());
        let str = String::from_utf8(data).unwrap();
        Self(str)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, RlpEncodable)]
pub struct AccountValue {
    pub nonce: u64,
    pub balance: u64,
    pub code_hash: B256,
    pub storage_root: B256,
}

impl AccountValue {
    pub fn new_eoa(nonce: u64, balance: u64) -> Self {
        Self { nonce, balance, code_hash: B256::ZERO, storage_root: B256::ZERO }
    }
}

impl Value for AccountValue {
    fn as_bytes(&self) -> Vec<u8> {
        let mut bytes = vec![];
        bytes.append(&mut self.nonce.to_le_bytes().to_vec());
        bytes.append(&mut self.balance.to_le_bytes().to_vec());
        bytes.append(&mut self.code_hash.to_vec());
        bytes.append(&mut self.storage_root.to_vec());
        bytes
    }

    fn from_bytes(data: &[u8]) -> Self {
        let nonce = u64::from_le_bytes(data[0..8].try_into().unwrap());
        let balance = u64::from_le_bytes(data[8..16].try_into().unwrap());
        let code_hash = data[16..48].try_into().unwrap();
        let storage_root = data[48..80].try_into().unwrap();
        Self { nonce, balance, code_hash, storage_root }
    }

    fn rlp_encode(&self) -> Vec<u8> {
        alloy_rlp::encode(self)
    }
}
