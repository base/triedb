use alloy_primitives::B256;

use crate::{
    location::Location,
    storage::value::{self, Value},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pointer {
    location: Location,
    hash: B256,
}

impl Pointer {
    pub fn new(location: Location, hash: B256) -> Self {
        Self { location, hash }
    }

    pub fn new_unhashed(location: Location) -> Self {
        Self {
            location,
            hash: B256::ZERO,
        }
    }

    pub fn hash(&self) -> B256 {
        self.hash
    }

    pub fn location(&self) -> Location {
        self.location
    }
}

impl Value for Pointer {
    fn to_bytes(self) -> Vec<u8> {
        let arr: [u8; 36] = self.into();
        arr.to_vec()
    }

    fn from_bytes(bytes: &[u8]) -> value::Result<Self> {
        let arr: [u8; 36] = bytes
            .try_into()
            .map_err(|_| value::Error::InvalidEncoding)?;
        Ok(Pointer::new(
            Location::from(u32::from_be_bytes(arr[..4].try_into().unwrap())),
            B256::from_slice(&arr[4..]),
        ))
    }
}

impl From<Pointer> for [u8; 36] {
    fn from(pointer: Pointer) -> Self {
        let mut data = [0; 36];
        let location: u32 = pointer.location().into();
        data[..4].copy_from_slice(&location.to_be_bytes());
        data[4..].copy_from_slice(pointer.hash().as_slice());
        data
    }
}
