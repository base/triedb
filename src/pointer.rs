use alloy_trie::nodes::RlpNode;

use crate::{
    location::Location,
    storage::value::{self, Value},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pointer {
    location: Location,
    rlp: RlpNode,
}

impl Pointer {
    pub fn new(location: Location, rlp: RlpNode) -> Self {
        Self { location, rlp }
    }

    pub fn new_unhashed(location: Location) -> Self {
        Self {
            location,
            rlp: RlpNode::from_rlp(&[]),
        }
    }

    pub fn rlp(&self) -> &RlpNode {
        &self.rlp
    }

    pub fn location(&self) -> Location {
        self.location
    }
}

impl Value for Pointer {
    fn to_bytes(self) -> Vec<u8> {
        let arr: [u8; 37] = self.into();
        arr.to_vec()
    }

    fn from_bytes(bytes: &[u8]) -> value::Result<Self> {
        let arr: [u8; 37] = bytes
            .try_into()
            .map_err(|_| value::Error::InvalidEncoding)?;
        Ok(Pointer::new(
            Location::from(u32::from_be_bytes(arr[..4].try_into().unwrap())),
            RlpNode::from_raw(&arr[4..]).ok_or(value::Error::InvalidEncoding)?,
        ))
    }
}

impl From<Pointer> for [u8; 37] {
    fn from(pointer: Pointer) -> Self {
        let mut data = [0; 37];
        let location: u32 = pointer.location().into();
        data[..4].copy_from_slice(&location.to_be_bytes());
        let rlp = pointer.rlp();
        data[4..4 + rlp.len()].copy_from_slice(&rlp);
        data
    }
}
