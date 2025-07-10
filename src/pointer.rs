use alloy_trie::nodes::RlpNode;

use crate::{
    location::Location,
    storage::value::{self, Value},
};
use alloy_primitives::{B256, U256};
use alloy_rlp::encode;
use proptest::prelude::*;

const BRANCH_FLAG: u8 = 0x01;
const HASH_FLAG: u8 = 0x02;

/// A pointer to a node in the trie.
/// This is a wrapper around a [Location] and an [RlpNode].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pointer {
    flags: u8,
    location: Location,
    rlp: RlpNode,
}

impl Pointer {
    /// Creates a new [Pointer] to a branch node from a [Location] and an [RlpNode].
    pub fn new_branch(location: Location, rlp: RlpNode) -> Self {
        Self::new_with_flags(location, BRANCH_FLAG | HASH_FLAG, rlp)
    }

    /// Creates a new [Pointer] to a leaf node from a [Location] and an [RlpNode].
    pub fn new_leaf(location: Location, rlp: RlpNode) -> Self {
        if rlp.is_hash() {
            Self::new_with_flags(location, HASH_FLAG, rlp)
        } else {
            Self::new_with_flags(location, 0, rlp)
        }
    }

    fn new_with_flags(location: Location, flags: u8, rlp: RlpNode) -> Self {
        Self { flags, location, rlp }
    }

    pub fn with_location(&self, location: Location) -> Self {
        Self { location, ..self.clone() }
    }

    /// Returns the [RlpNode] wrapped by the [Pointer].
    pub fn rlp(&self) -> &RlpNode {
        &self.rlp
    }

    /// Returns the [Location] wrapped by the [Pointer].
    pub fn location(&self) -> Location {
        self.location
    }

    pub fn is_branch(&self) -> bool {
        self.flags & BRANCH_FLAG == BRANCH_FLAG
    }

    pub fn is_hash(&self) -> bool {
        self.flags & HASH_FLAG == HASH_FLAG
    }
}

impl Arbitrary for Pointer {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        (any::<Location>(), u256_or_hash(), any::<bool>())
            .prop_map(|(location, rlp, is_branch)| {
                if is_branch {
                    Pointer::new_branch(location, rlp)
                } else {
                    Pointer::new_leaf(location, rlp)
                }
            })
            .boxed()
    }
}

impl Value for Pointer {
    fn size(&self) -> usize {
        37 // Fixed size: 4 bytes location + 33 bytes max RLP
    }

    fn serialize_into(&self, buf: &mut [u8]) -> value::Result<usize> {
        if buf.len() < 37 {
            return Err(value::Error::InvalidEncoding);
        }

        let arr: [u8; 37] = self.into();
        buf[..37].copy_from_slice(&arr);
        Ok(37)
    }

    fn from_bytes(bytes: &[u8]) -> value::Result<Self> {
        let arr: [u8; 37] = bytes.try_into().map_err(|_| value::Error::InvalidEncoding)?;
        let flags = arr[4];
        let rlp = if flags & HASH_FLAG == HASH_FLAG {
            RlpNode::word_rlp(&B256::from_slice(&arr[5..37]))
        } else {
            // Because the RLP string must be 1-32 bytes, we can safely use the first byte to determine
            // the length. If the first byte is less than 0x80, then this byte is the actual
            // encoded value. Otherwise, the length is first_rlp_byte - 0x80, and the remaining
            // bytes are the encoded U256 value.
            let first_rlp_byte = arr[5];
            if first_rlp_byte < 0x80 {
                RlpNode::from_raw(&[first_rlp_byte]).unwrap()
            } else if first_rlp_byte <= 0xa0 {
                let rlp_len = first_rlp_byte - 0x80;
                RlpNode::from_raw(&arr[5..6 + rlp_len as usize]).unwrap()
            } else if first_rlp_byte >= 0xc0 && first_rlp_byte <= 0xdf {
                let rlp_len = first_rlp_byte - 0xc0;
                RlpNode::from_raw(&arr[5..6 + rlp_len as usize]).unwrap()
            } else {
                return Err(value::Error::InvalidEncoding);
            }
        };
        Ok(Pointer::new_with_flags(Location::from(u32::from_be_bytes(arr[..4].try_into().unwrap())), flags, rlp))
    }
}

impl From<Pointer> for [u8; 37] {
    fn from(pointer: Pointer) -> Self {
        (&pointer).into()
    }
}

impl From<&Pointer> for [u8; 37] {
    // FIXME: flags only use a single bit, so we can combine flags from several pointers into a
    // single byte. This is particularly useful for branch nodes, which can have up to 16 children,
    // saving 14 bytes total.
    fn from(pointer: &Pointer) -> Self {
        let mut data = [0u8; 37];
        let location: u32 = pointer.location().into();
        data[..4].copy_from_slice(&location.to_be_bytes());

        // Determine flags and content
        let rlp = pointer.rlp();
        let content = if rlp.is_hash() {
            &rlp[1..]
        } else {
            rlp.as_ref()
        };

        data[4] = pointer.flags;
        let content_len = content.len().min(33);
        data[5..5 + content_len].copy_from_slice(&content[..content_len]);
        data
    }
}

fn u256_or_hash() -> impl Strategy<Value = RlpNode> {
    prop_oneof![arb_u256_rlp(), arb_hash_rlp()]
}

fn arb_u256_rlp() -> impl Strategy<Value = RlpNode> {
    any::<U256>().prop_map(|u| RlpNode::from_rlp(&encode(u))).boxed()
}

fn arb_hash_rlp() -> impl Strategy<Value = RlpNode> {
    any::<B256>().prop_map(|h: B256| RlpNode::word_rlp(&h)).boxed()
}

#[cfg(test)]
mod tests {
    use alloy_primitives::hex;
    use alloy_rlp::encode;
    use alloy_trie::EMPTY_ROOT_HASH;

    use super::*;

    #[test]
    fn test_pointer_to_bytes() {
        let rlp_hash = RlpNode::word_rlp(&EMPTY_ROOT_HASH);
        let pointer = Pointer::new_branch(Location::for_cell(1), rlp_hash);
        let bytes = pointer.serialize().unwrap();
        let mut expected = vec![0, 0, 0, 1, 3];
        expected.extend(EMPTY_ROOT_HASH);
        assert_eq!(bytes, expected);

        let short_rlp = RlpNode::from_rlp(&encode(42u64));
        let pointer = Pointer::new_leaf(Location::for_cell(1), short_rlp);
        let bytes = pointer.serialize().unwrap();
        let mut expected = vec![0, 0, 0, 1, 0, 42];
        expected.extend([0; 31]);
        assert_eq!(bytes, expected);

        let zero_rlp = RlpNode::from_rlp(&encode(0u64));
        let pointer = Pointer::new_leaf(Location::for_cell(1), zero_rlp);
        let bytes = pointer.serialize().unwrap();
        let mut expected = vec![0, 0, 0, 1, 0, 128];
        expected.extend([0; 31]);
        assert_eq!(bytes, expected);

        let short_string_rlp = RlpNode::from_rlp(&encode("hello world"));
        let pointer = Pointer::new_leaf(Location::for_cell(1), short_string_rlp);
        let bytes = pointer.serialize().unwrap();
        let mut expected = vec![0, 0, 0, 1, 0, 139];
        expected.extend(b"hello world");
        expected.extend([0; 20]);
        assert_eq!(bytes, expected);
 
        // Hex encoding of ["abc", 12345]
        let short_leaf_rlp = RlpNode::from_rlp(&hex!("c783616263823039"));
        let pointer = Pointer::new_leaf(Location::for_cell(1), short_leaf_rlp);
        let bytes = pointer.serialize().unwrap();
        let mut expected = vec![0, 0, 0, 1, 0, 0xc7, 0x83, 0x61, 0x62, 0x63, 0x82, 0x30, 0x39];
        expected.extend([0; 24]);
        assert_eq!(bytes, expected);
    }

    #[test]
    fn test_pointer_from_bytes() {
        let mut rlp_hash_bytes = vec![0, 0, 0, 1, 3];
        rlp_hash_bytes.extend(&EMPTY_ROOT_HASH);
        let pointer = Pointer::from_bytes(&rlp_hash_bytes).unwrap();
        assert_eq!(pointer.location(), Location::for_cell(1));
        assert_eq!(pointer.rlp(), &RlpNode::word_rlp(&EMPTY_ROOT_HASH));

        let mut short_rlp_bytes = vec![0, 0, 0, 1, 0, 42];
        short_rlp_bytes.extend([0; 31]);
        let pointer = Pointer::from_bytes(&short_rlp_bytes).unwrap();
        assert_eq!(pointer.location(), Location::for_cell(1));
        assert_eq!(pointer.rlp(), &RlpNode::from_rlp(&encode(42u64)));

        let mut zero_rlp_bytes = vec![0, 0, 0, 1, 0, 128];
        zero_rlp_bytes.extend([0; 31]);
        let pointer = Pointer::from_bytes(&zero_rlp_bytes).unwrap();
        assert_eq!(pointer.location(), Location::for_cell(1));
        assert_eq!(pointer.rlp(), &RlpNode::from_rlp(&encode(0u64)));

        let mut short_string_rlp_bytes = vec![0, 0, 0, 1, 0, 139];
        short_string_rlp_bytes.extend(b"hello world");
        short_string_rlp_bytes.extend([0; 20]);
        let pointer = Pointer::from_bytes(&short_string_rlp_bytes).unwrap();
        assert_eq!(pointer.location(), Location::for_cell(1));
        assert_eq!(pointer.rlp(), &RlpNode::from_rlp(&encode("hello world")));

        let mut short_leaf_rlp_bytes = vec![0, 0, 0, 1, 0, 0xc7, 0x83, 0x61, 0x62, 0x63, 0x82, 0x30, 0x39];
        short_leaf_rlp_bytes.extend([0; 24]);
        let pointer = Pointer::from_bytes(&short_leaf_rlp_bytes).unwrap();
        assert_eq!(pointer.location(), Location::for_cell(1));
        assert_eq!(pointer.rlp(), &RlpNode::from_rlp(&hex!("c783616263823039")));
    }

    proptest! {
        #[test]
        fn fuzz_pointer_to_from_bytes(pointer: Pointer) {
            let bytes = pointer.serialize().unwrap();
            let decoded = Pointer::from_bytes(&bytes).unwrap();
            prop_assert_eq!(pointer, decoded);
        }
    }
}
