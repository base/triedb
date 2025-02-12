use alloy_primitives::{B256, U256};
use std::fmt::Debug;

pub trait Account<'a>:
    Debug + TryFrom<&'a [u8], Error: Debug> + TryInto<&'a [u8], Error: Debug>
{
    fn balance(&self) -> U256;
    fn nonce(&self) -> u64;
    fn code_hash(&self) -> B256;
    fn storage_root(&self) -> B256;
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
        data[0..32].copy_from_slice(&balance.as_le_slice());
        data[32..40].copy_from_slice(&nonce.to_le_bytes());
        data[40..72].copy_from_slice(&code_hash.as_slice());
        data[72..104].copy_from_slice(&storage_root.as_slice());
        Self { data }
    }
}

impl<'a> Account<'a> for AccountSlice<'a> {
    fn balance(&self) -> U256 {
        U256::from_le_slice(&self.data[0..32])
    }

    fn nonce(&self) -> u64 {
        u64::from_le_bytes(unsafe { *self.data.as_ptr().add(32).cast() })
    }

    fn code_hash(&self) -> B256 {
        B256::from_slice(&self.data[40..72])
    }

    fn storage_root(&self) -> B256 {
        B256::from_slice(&self.data[72..104])
    }
}

impl<'a> TryFrom<&'a [u8]> for AccountSlice<'a> {
    type Error = ();

    fn try_from(data: &'a [u8]) -> Result<Self, Self::Error> {
        if data.len() < 104 {
            return Err(());
        }
        Ok(Self { data })
    }
}

impl<'a> From<AccountSlice<'a>> for &'a [u8] {
    fn from(slice: AccountSlice<'a>) -> Self {
        slice.data
    }
}
