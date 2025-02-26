use alloy_rlp::{encode, Decodable};
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
    fn to_bytes(&self) -> Vec<u8> {
        let arr: [u8; 37] = self.into();
        arr.to_vec()
    }

    fn from_bytes(bytes: &[u8]) -> value::Result<Self> {
        let arr: [u8; 37] = bytes
            .try_into()
            .map_err(|_| value::Error::InvalidEncoding)?;
        let first_rlp_byte = arr[4];
        // Because the RLP string must be 1-33 bytes, we can safely use the first byte to determine the length.
        // If the first byte is less than 0x80, then this byte is the actual encoded value.
        // Otherwise, the length is first_rlp_byte - 0x80.
        let rlp = if first_rlp_byte < 0x80 {
            RlpNode::from_raw(&[first_rlp_byte]).unwrap()
        } else if first_rlp_byte <= 0xa0 {
            let rlp_len = first_rlp_byte - 0x80;
            RlpNode::from_raw(&arr[4..5 + rlp_len as usize]).unwrap()
        } else {
            return Err(value::Error::InvalidEncoding);
        };
        Ok(Pointer::new(
            Location::from(u32::from_be_bytes(arr[..4].try_into().unwrap())),
            rlp,
        ))
    }
}

impl From<Pointer> for [u8; 37] {
    fn from(pointer: Pointer) -> Self {
        let mut data = [0; 37];
        let location: u32 = pointer.location().into();
        data[..4].copy_from_slice(&location.to_be_bytes());
        let rlp = pointer.rlp();
        data[4..4 + rlp.len()].copy_from_slice(rlp);
        data
    }
}

impl From<&Pointer> for [u8; 37] {
    fn from(pointer: &Pointer) -> Self {
        let mut data = [0; 37];
        let location: u32 = pointer.location().into();
        data[..4].copy_from_slice(&location.to_be_bytes());
        let rlp = pointer.rlp();
        data[4..4 + rlp.len()].copy_from_slice(&rlp);
        data
    }
}

#[cfg(test)]
mod tests {
    use alloy_rlp::encode;
    use alloy_trie::EMPTY_ROOT_HASH;

    use super::*;

    #[test]
    fn test_pointer_to_bytes() {
        let rlp_hash = RlpNode::word_rlp(&EMPTY_ROOT_HASH);
        let pointer = Pointer::new(Location::for_cell(1), rlp_hash);
        let bytes = pointer.to_bytes();
        let mut expected = vec![0, 0, 0, 1, 160];
        expected.extend(EMPTY_ROOT_HASH);
        assert_eq!(bytes, expected);

        let short_rlp = RlpNode::from_rlp(&encode(42u64));
        let pointer = Pointer::new(Location::for_cell(1), short_rlp);
        let bytes = pointer.to_bytes();
        let mut expected = vec![0, 0, 0, 1, 42];
        expected.extend([0; 32]);
        assert_eq!(bytes, expected);

        let zero_rlp = RlpNode::from_rlp(&encode(0u64));
        let pointer = Pointer::new(Location::for_cell(1), zero_rlp);
        let bytes = pointer.to_bytes();
        let mut expected = vec![0, 0, 0, 1, 128];
        expected.extend([0; 32]);
        assert_eq!(bytes, expected);

        let short_string_rlp = RlpNode::from_rlp(&encode("hello world"));
        let pointer = Pointer::new(Location::for_cell(1), short_string_rlp);
        let bytes = pointer.to_bytes();
        let mut expected = vec![0, 0, 0, 1, 139];
        expected.extend(b"hello world");
        expected.extend([0; 21]);
        assert_eq!(bytes, expected);
    }

    #[test]
    fn test_pointer_from_bytes() {
        let mut rlp_hash_bytes = vec![0, 0, 0, 1, 160];
        rlp_hash_bytes.extend(&EMPTY_ROOT_HASH);
        let pointer = Pointer::from_bytes(&rlp_hash_bytes).unwrap();
        assert_eq!(pointer.location(), Location::for_cell(1));
        assert_eq!(pointer.rlp(), &RlpNode::word_rlp(&EMPTY_ROOT_HASH));

        let mut short_rlp_bytes = vec![0, 0, 0, 1, 42];
        short_rlp_bytes.extend([0; 32]);
        let pointer = Pointer::from_bytes(&short_rlp_bytes).unwrap();
        assert_eq!(pointer.location(), Location::for_cell(1));
        assert_eq!(pointer.rlp(), &RlpNode::from_rlp(&encode(42u64)));

        let mut zero_rlp_bytes = vec![0, 0, 0, 1, 128];
        zero_rlp_bytes.extend([0; 32]);
        let pointer = Pointer::from_bytes(&zero_rlp_bytes).unwrap();
        assert_eq!(pointer.location(), Location::for_cell(1));
        assert_eq!(pointer.rlp(), &RlpNode::from_rlp(&encode(0u64)));

        let mut short_string_rlp_bytes = vec![0, 0, 0, 1, 139];
        short_string_rlp_bytes.extend(b"hello world");
        short_string_rlp_bytes.extend([0; 21]);
        let pointer = Pointer::from_bytes(&short_string_rlp_bytes).unwrap();
        assert_eq!(pointer.location(), Location::for_cell(1));
        assert_eq!(pointer.rlp(), &RlpNode::from_rlp(&encode("hello world")));
    }
}
