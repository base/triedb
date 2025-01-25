use crate::value::{Value, Error};
use alloy_primitives::U256;
use bytes::buf::BufMut;
use alloy_rlp::{Encodable, RlpEncodable};

// 8 for nonce, 32 for balance, 32 for code hash, 32 for storage root
const NUM_BYTES: usize = 104;

#[derive(Debug, PartialEq, Eq)]
pub struct Account<'v>(&'v [u8]);

impl<'v> Account<'v> {
    pub fn new(nonce: u64, balance: U256, code_hash: [u8; 32], storage_root: [u8; 32], data: &'v mut [u8]) -> Self {
        data[0..8].copy_from_slice(&nonce.to_be_bytes());
        data[8..40].copy_from_slice(&balance.as_le_bytes());
        data[40..72].copy_from_slice(&code_hash);
        data[72..104].copy_from_slice(&storage_root);
        Self(data)
    }
}

impl<'v> Value<'v> for Account<'v> {
    fn as_bytes(&self) -> &'v [u8] {
        self.0
    }

    fn try_from_bytes(data: &'v [u8]) -> Result<Self, Error> {
        if data.len() != NUM_BYTES {
            return Err(Error::InvalidLength);
        }
        Ok(Self(data))
    }
}

impl<'v> Encodable for Account<'v> {
    fn length(&self) -> usize {
        135
    }

    fn encode(&self, out: &mut dyn BufMut) {
        let rlp_account = RLPAccount {
            nonce: u64::from_be_bytes(self.0[0..8].try_into().unwrap()),
            balance: U256::from_le_slice(&self.0[8..40]),
            code_hash: self.0[40..72].try_into().unwrap(),
            storage_root: self.0[72..104].try_into().unwrap(),
        };
        rlp_account.encode(out);
    }
}

#[derive(Debug, PartialEq, Eq, RlpEncodable)]
struct RLPAccount {
    nonce: u64,
    balance: U256,
    code_hash: [u8; 32],
    storage_root: [u8; 32],
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_as_from_bytes() {
        let data = [42u8; 104];
        let account = Account::try_from_bytes(&data).unwrap();
        assert_eq!(account.as_bytes(), &data);
    }

    #[test]
    fn test_try_from_bytes_invalid_length() {
        let data = [0u8; 0];
        let result = Account::try_from_bytes(&data);
        assert!(result.is_err());

        let data = [0u8; 103];
        let result = Account::try_from_bytes(&data);
        assert!(result.is_err());

        let data = [0u8; 105];
        let result = Account::try_from_bytes(&data);
        assert!(result.is_err());
    }

    #[test]
    fn test_encode() {
        let nonce = 1;
        let balance = U256::from(2);
        let code_hash = [42u8; 32];
        let storage_root = [255u8; 32];

        let mut data = [0u8; 104];
        let account = Account::new(nonce, balance, code_hash, storage_root, &mut data);
        let rlp_account = RLPAccount {nonce, balance, code_hash, storage_root };

        let mut out1 = Vec::new();
        account.encode(&mut out1);
        let mut out2 = Vec::new();
        rlp_account.encode(&mut out2);
        assert_eq!(out1, out2);

        let nonce = u64::MAX;
        let balance = U256::MAX;
        let code_hash = [255u8; 32];
        let storage_root = [0u8; 32];

        let mut data = [0u8; 104];
        let account = Account::new(nonce, balance, code_hash, storage_root, &mut data);
        let rlp_account = RLPAccount {nonce, balance, code_hash, storage_root };

        let mut out1 = Vec::new();
        account.encode(&mut out1);
        let mut out2 = Vec::new();
        rlp_account.encode(&mut out2);
        assert_eq!(out1, out2);
    }
}
