mod account;
mod storage;

pub use crate::value::account::Account;
pub use crate::value::storage::StorageSlot;

use std::fmt::Debug;
use alloy_rlp::Encodable;

pub trait Value<'v>: Debug + Encodable + Sized {
    fn as_bytes(&self) -> &'v [u8];
    fn try_from_bytes(data: &'v [u8]) -> Result<Self, Error>;
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    InvalidLength,
}
