use alloy_primitives::B256;
use alloy_rlp::{encode, BufMut, Encodable};
use alloy_trie::{
    nodes::{BranchNode, ExtensionNodeRef, LeafNodeRef, RlpNode},
    Nibbles, TrieMask,
};
use proptest::prelude::{any, prop, Strategy};
use proptest_derive::Arbitrary;

use crate::{
    pointer::Pointer,
    storage::value::{self, Value},
};

#[derive(Debug, Clone, PartialEq, Eq, Arbitrary)]
pub enum Node<V> {
    AccountLeaf {
        prefix: Nibbles,
        value: V,
        storage_root: Option<Pointer>,
    },
    StorageLeaf {
        prefix: Nibbles,
        value: V,
    },
    Branch {
        prefix: Nibbles,
        #[proptest(strategy = "arb_children()")]
        children: [Option<Pointer>; 16],
    },
}

#[derive(Debug, Clone, Copy)]
pub enum LeafType {
    AccountLeaf,
    StorageLeaf,
}

impl<V: Value> Node<V> {
    pub fn new_leaf(prefix: Nibbles, value: V, leaf_type: LeafType) -> Self {
        assert!(
            prefix.len() <= 64,
            "account and storage leaf prefix's must be at most 64 nibbles"
        );
        match leaf_type {
            LeafType::AccountLeaf => Node::new_account_leaf(prefix, value, None),
            LeafType::StorageLeaf => Node::new_storage_leaf(prefix, value),
        }
    }

    pub fn new_account_leaf(prefix: Nibbles, value: V, storage_root: Option<Pointer>) -> Self {
        Self::AccountLeaf {
            prefix,
            value,
            storage_root,
        }
    }

    pub fn new_storage_leaf(prefix: Nibbles, value: V) -> Self {
        Self::StorageLeaf { prefix, value }
    }

    pub fn new_branch(prefix: Nibbles) -> Self {
        Self::Branch {
            prefix,
            children: [const { None }; 16],
        }
    }

    pub fn prefix(&self) -> &Nibbles {
        match self {
            Self::StorageLeaf { prefix, .. } => prefix,
            Self::AccountLeaf { prefix, .. } => prefix,
            Self::Branch { prefix, .. } => prefix,
        }
    }

    pub fn set_prefix(&mut self, new_prefix: Nibbles) {
        match self {
            Self::StorageLeaf { prefix, .. } => *prefix = new_prefix,
            Self::AccountLeaf { prefix, .. } => *prefix = new_prefix,
            Self::Branch { prefix, .. } => *prefix = new_prefix,
        }
    }

    pub fn has_children(&self) -> bool {
        matches!(self, Self::Branch { .. } | Self::AccountLeaf { .. })
    }

    pub fn is_branch(&self) -> bool {
        matches!(self, Self::Branch { .. })
    }

    pub fn enumerate_children(&self) -> Vec<(u8, &Pointer)> {
        match self {
            Self::AccountLeaf { storage_root, .. } => [storage_root]
                .iter()
                .enumerate()
                .filter_map(|(i, child)| child.as_ref().map(|p| (i as u8, p)))
                .collect(),
            Self::Branch { children, .. } => children
                .iter()
                .enumerate()
                .filter_map(|(i, child)| child.as_ref().map(|p| (i as u8, p)))
                .collect(),
            _ => panic!("cannot enumerate children of non-branch node"),
        }
    }

    pub fn child(&self, index: u8) -> Option<&Pointer> {
        match self {
            Self::Branch { children, .. } => children[index as usize].as_ref(),
            _ => panic!("cannot get child of leaf node"),
        }
    }

    pub fn direct_child(&self) -> Option<&Pointer> {
        match self {
            Self::AccountLeaf { storage_root, .. } => storage_root.as_ref(),
            _ => panic!("cannot get child of leaf node"),
        }
    }

    pub fn set_child(&mut self, index: u8, child: Pointer) {
        match self {
            Self::AccountLeaf { storage_root, .. } => *storage_root = Some(child),
            Self::Branch { children, .. } => children[index as usize] = Some(child),
            _ => panic!("cannot set child of non-branch node"),
        }
    }

    pub fn remove_child(&mut self, index: u8) {
        match self {
            Self::AccountLeaf { storage_root, .. } => *storage_root = None,
            Self::Branch { children, .. } => children[index as usize] = None,
            _ => panic!("cannot set child of non-branch node"),
        }
    }

    pub fn value(&self) -> Option<&V> {
        match self {
            Self::StorageLeaf { value, .. } => Some(value),
            Self::AccountLeaf { value, .. } => Some(value),
            _ => panic!("cannot get value of non-leaf node"),
        }
    }

    pub fn into_value(self) -> V {
        match self {
            Self::AccountLeaf { value, .. } => value,
            Self::StorageLeaf { value, .. } => value,
            _ => panic!("cannot get value of non-leaf node"),
        }
    }
}

impl<V: Value + Encodable> Node<V> {
    pub fn rlp_encode(&self) -> RlpNode {
        RlpNode::from_rlp(&encode(self))
    }
}

impl<V: Value> Value for Node<V> {
    fn size(&self) -> usize {
        match self {
            Self::StorageLeaf { prefix, value } => {
                let packed_prefix_length = (prefix.len() + 1) / 2;
                2 + packed_prefix_length + value.size() // 2 bytes for type and prefix length
            }
            Self::AccountLeaf { prefix, value, .. } => {
                let packed_prefix_length = (prefix.len() + 1) / 2;
                2 + packed_prefix_length + 37 + value.size() // 2 bytes for type and prefix length, 37 for storage root
            }
            Self::Branch { prefix, .. } => {
                let packed_prefix_length = (prefix.len() + 1) / 2;
                2 + packed_prefix_length + 2 + 16 * 37 // 2 bytes for type and prefix length, 2 for bitmask, 37 for each child pointer
            }
        }
    }

    fn serialize_into(&self, buf: &mut [u8]) -> value::Result<usize> {
        match self {
            Self::StorageLeaf { prefix, value } => {
                let prefix_length = prefix.len();
                let packed_prefix_length = (prefix_length + 1) / 2;
                let total_size = 2 + packed_prefix_length + value.size();
                if buf.len() < total_size {
                    return Err(value::Error::InvalidEncoding);
                }

                buf[0] = 0; // StorageLeaf type
                buf[1] = prefix_length as u8;
                prefix.pack_to(buf[2..2 + packed_prefix_length].as_mut());
                let bytes_written = value.serialize_into(&mut buf[2 + packed_prefix_length..])?;

                Ok(2 + prefix_length + bytes_written)
            }
            Self::AccountLeaf {
                prefix,
                value,
                storage_root,
            } => {
                let prefix_length = prefix.len();
                let packed_prefix_length = (prefix_length + 1) / 2;
                let total_size = 2 + packed_prefix_length + 37 + value.size();
                if buf.len() < total_size {
                    return Err(value::Error::InvalidEncoding);
                }

                buf[0] = 1; // AccountLeaf type
                buf[1] = prefix_length as u8;
                prefix.pack_to(buf[2..2 + packed_prefix_length].as_mut());

                let storage_offset = 2 + packed_prefix_length;
                if let Some(storage) = storage_root {
                    // Serialize the pointer
                    storage.serialize_into(&mut buf[storage_offset..storage_offset + 37])?;
                } else {
                    // Fill with zeros if no storage root
                    buf[storage_offset..storage_offset + 37].fill(0);
                }

                let bytes_written = value.serialize_into(&mut buf[storage_offset + 37..])?;

                Ok(storage_offset + 37 + bytes_written)
            }
            Self::Branch { prefix, children } => {
                let prefix_length = prefix.len();
                let packed_prefix_length = (prefix_length + 1) / 2;
                let mut total_size = 2 + packed_prefix_length + 2; // Type, prefix length, bitmask
                for _ in children.iter().flatten() {
                    total_size += 37; // Each pointer is 37 bytes
                }

                if buf.len() < total_size {
                    return Err(value::Error::InvalidEncoding);
                }

                buf[0] = 2; // Branch type
                buf[1] = prefix_length as u8;
                prefix.pack_to(buf[2..2 + packed_prefix_length].as_mut());

                // Calculate and store the children bitmask
                let children_bitmask = children
                    .iter()
                    .enumerate()
                    .map(|(idx, child)| (child.is_some() as u16) << (15 - idx))
                    .sum::<u16>();
                buf[2 + packed_prefix_length..2 + packed_prefix_length + 2]
                    .copy_from_slice(&children_bitmask.to_be_bytes());

                // Store each child pointer
                let mut offset = 2 + packed_prefix_length + 2;
                for child in children.iter() {
                    if let Some(child) = child {
                        child.serialize_into(&mut buf[offset..offset + 37])?;
                    } else {
                        buf[offset..offset + 37].fill(0);
                    }
                    offset += 37;
                }

                Ok(offset)
            }
        }
    }

    fn from_bytes(bytes: &[u8]) -> value::Result<Self> {
        let first_byte = bytes[0];
        if first_byte == 0 {
            let prefix_length = bytes[1] as usize;
            let packed_prefix_length = (prefix_length + 1) / 2;
            let mut prefix = Nibbles::unpack(&bytes[2..2 + packed_prefix_length]);
            prefix.truncate(prefix_length);
            let value = V::from_bytes(&bytes[packed_prefix_length + 2..])?;
            Ok(Self::StorageLeaf { prefix, value })
        } else if first_byte == 1 {
            let prefix_length = bytes[1] as usize;
            let packed_prefix_length = (prefix_length + 1) / 2;
            let mut prefix = Nibbles::unpack(&bytes[2..2 + packed_prefix_length]);
            prefix.truncate(prefix_length);
            let storage_root_bytes =
                &bytes[2 + packed_prefix_length..2 + packed_prefix_length + 37];
            let value = V::from_bytes(&bytes[2 + packed_prefix_length + 37..])?;

            let storage_root = if storage_root_bytes == [0; 37] {
                None
            } else {
                Some(Pointer::from_bytes(storage_root_bytes)?)
            };

            Ok(Self::AccountLeaf {
                prefix,
                value,
                storage_root,
            })
        } else {
            let prefix_length = bytes[1] as usize;
            let packed_prefix_length = (prefix_length + 1) / 2;
            let mut prefix = Nibbles::unpack(&bytes[2..2 + packed_prefix_length]);
            prefix.truncate(prefix_length);
            let children_bitmask = u16::from_be_bytes(
                bytes[2 + packed_prefix_length..2 + packed_prefix_length + 2]
                    .try_into()
                    .unwrap(),
            );
            let mut children = [const { None }; 16];
            for (i, child) in children.iter_mut().enumerate() {
                if children_bitmask & (1 << (15 - i)) == 0 {
                    continue;
                }
                let child_offset = 4 + packed_prefix_length + i * 37;
                let child_bytes = &bytes[child_offset..child_offset + 37];
                *child = Some(Pointer::from_bytes(child_bytes)?);
            }
            Ok(Self::Branch { prefix, children })
        }
    }
}

impl<V: Value + Encodable> Encodable for Node<V> {
    fn encode(&self, out: &mut dyn BufMut) {
        match self {
            Self::StorageLeaf { prefix, value } => {
                let value_rlp = encode(value);
                LeafNodeRef {
                    key: prefix,
                    value: &value_rlp,
                }
                .encode(out);
            }
            Self::AccountLeaf { prefix, value, .. } => {
                let value_rlp = encode(value);
                LeafNodeRef {
                    key: prefix,
                    value: &value_rlp,
                }
                .encode(out);
            }
            Self::Branch { prefix, children } => {
                if prefix.is_empty() {
                    BranchNode {
                        stack: children
                            .iter()
                            .filter_map(|child| child.as_ref().map(|p| p.rlp().clone()))
                            .collect(),
                        state_mask: TrieMask::new(
                            children
                                .iter()
                                .enumerate()
                                .map(|(i, child)| (child.is_some() as u16) << i)
                                .sum(),
                        ),
                    }
                    .encode(out);
                } else {
                    let branch_rlp = encode(&BranchNode {
                        stack: children
                            .iter()
                            .filter_map(|child| child.as_ref().map(|p| p.rlp().clone()))
                            .collect(),
                        state_mask: TrieMask::new(
                            children
                                .iter()
                                .enumerate()
                                .map(|(i, child)| (child.is_some() as u16) << i)
                                .sum(),
                        ),
                    });
                    ExtensionNodeRef {
                        key: prefix,
                        child: &RlpNode::from_rlp(&branch_rlp),
                    }
                    .encode(out);
                }
            }
        }
    }

    fn length(&self) -> usize {
        match self {
            Self::StorageLeaf { prefix, value } => {
                // this just has to be an estimate for `Vec::with_capacity`
                prefix.len() + value.size() + 10 // 10 is just a buffer
            }
            Self::AccountLeaf { prefix, value, .. } => {
                // this just has to be an estimate for `Vec::with_capacity`
                prefix.len() + value.size() + 10 // 10 is just a buffer
            }
            Self::Branch { prefix, children } => {
                if prefix.is_empty() {
                    BranchNode {
                        stack: children
                            .iter()
                            .filter_map(|child| child.as_ref().map(|p| p.rlp().clone()))
                            .collect(),
                        state_mask: TrieMask::new(
                            children
                                .iter()
                                .enumerate()
                                .map(|(i, child)| (child.is_some() as u16) << i)
                                .sum(),
                        ),
                    }
                    .length()
                } else {
                    ExtensionNodeRef {
                        key: prefix,
                        // hack: we know that a branch node will always be a
                        // RlpNode hash. since we only need the length, we use
                        // a dummy zero value here.
                        child: &RlpNode::word_rlp(&B256::ZERO),
                    }
                    .length()
                }
            }
        }
    }
}

fn arb_children() -> impl Strategy<Value = [Option<Pointer>; 16]> {
    (prop::collection::vec(any::<Pointer>(), 2..16), 1..15).prop_map(|(children, spacing)| {
        let mut result = [const { None }; 16];
        for (i, child) in children.iter().enumerate() {
            result[(i + spacing as usize) % 16] = Some(child.clone());
        }
        result
    })
}

#[cfg(test)]
mod tests {
    use alloy_primitives::{b256, hex, B256, U256};
    use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
    use proptest::prelude::*;

    use crate::account::AccountVec;

    use super::*;

    #[test]
    fn test_storage_leaf_node_serialize() {
        let node = Node::new_storage_leaf(Nibbles::from_nibbles([0xa, 0xb]), vec![4, 5, 6]);
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x0002ab040506"));

        let node = Node::new_storage_leaf(Nibbles::from_nibbles([0xa, 0xb, 0xc]), vec![4, 5, 6, 7]);
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x0003abc004050607"));

        let node = Node::new_storage_leaf(Nibbles::new(), vec![0xf, 0xf, 0xf, 0xf]);
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x00000f0f0f0f"));
    }

    #[test]
    fn test_account_leaf_node_serialize() {
        let node = Node::new_account_leaf(Nibbles::from_nibbles([0xa, 0xb]), vec![4, 5, 6], None);
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x0102ab00000000000000000000000000000000000000000000000000000000000000000000000000040506"));

        let node = Node::new_account_leaf(
            Nibbles::from_nibbles([0xa, 0xb, 0xc]),
            vec![4, 5, 6, 7],
            None,
        );
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x0103abc00000000000000000000000000000000000000000000000000000000000000000000000000004050607"));

        let node = Node::new_account_leaf(Nibbles::new(), vec![0xf, 0xf, 0xf, 0xf], None);
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x0100000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f"));
    }

    #[test]
    fn test_branch_node_serialize() {
        let mut node: Node<Vec<u8>> = Node::new_branch(Nibbles::new());
        let hash1 = b256!("0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef");
        let hash2 = b256!("0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
        node.set_child(0, Pointer::new(42.into(), RlpNode::word_rlp(&hash1)));
        node.set_child(11, Pointer::new(11.into(), RlpNode::word_rlp(&hash2)));
        let bytes = node.serialize().unwrap();
        // branch, no prefix
        let mut expected = Vec::from([2, 0]);
        // children bitmask (10000000 00010000)
        expected.extend([128, 16]);
        // child 0
        expected.extend([0, 0, 0, 42, 160]);
        expected.extend(hash1.as_slice());
        // children 1-10
        expected.extend(vec![0; 37 * 10]);
        // child 11
        expected.extend([0, 0, 0, 11, 160]);
        expected.extend(hash2.as_slice());
        // children 12-15
        expected.extend(vec![0; 37 * 4]);
        assert_eq!(bytes, expected);

        let mut node: Node<Vec<u8>> =
            Node::new_branch(Nibbles::from_nibbles([0xa, 0xb, 0xc, 0xd, 0xe]));
        let hash1 = b256!("0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef");
        let hash2 = b256!("0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
        node.set_child(2, Pointer::new(2.into(), RlpNode::word_rlp(&hash1)));
        node.set_child(3, Pointer::new(3.into(), RlpNode::word_rlp(&hash2)));
        let bytes = node.serialize().unwrap();
        // branch, length, prefix
        let mut expected = Vec::from([2, 5, 171, 205, 224]);
        // children bitmask (00110000 00000000)
        expected.extend([48, 0]);
        // children 0-1
        expected.extend([0; 37 * 2]);
        // child 2
        expected.extend([0, 0, 0, 2, 160]);
        expected.extend(hash1.as_slice());
        // child 3
        expected.extend([0, 0, 0, 3, 160]);
        expected.extend(hash2.as_slice());
        // children 4-15
        expected.extend([0; 37 * 12]);
        assert_eq!(bytes, expected);

        let mut node: Node<Vec<u8>> = Node::new_branch(Nibbles::from_nibbles([0x0, 0x0]));
        let v1 = encode(1u8);
        let v2 = encode("hello world");
        node.set_child(1, Pointer::new(99999.into(), RlpNode::from_rlp(&v1)));
        node.set_child(2, Pointer::new(8675309.into(), RlpNode::from_rlp(&v2)));
        let bytes = node.serialize().unwrap();

        // branch, length, prefix
        let mut expected = Vec::from([2, 2, 0]);
        // children bitmask (01100000 00000000)
        expected.extend([96, 0]);
        // child 0
        expected.extend([0; 37]);
        // child 1
        expected.extend([0, 1, 134, 159]);
        expected.extend(v1);
        expected.extend([0; 32]);
        // child 2
        expected.extend([0, 132, 95, 237]);
        expected.extend(v2);
        expected.extend([0; 21]);
        // children 3-15
        expected.extend([0; 37 * 13]);
        assert_eq!(bytes, expected);
    }

    #[test]
    fn test_leaf_node_encode() {
        let account = AccountVec::new(U256::from(1), 0, B256::ZERO, B256::ZERO);
        let node = Node::new_account_leaf(Nibbles::new(), account, None);
        let mut bytes = vec![];
        node.encode(&mut bytes);
        assert_eq!(bytes, hex!("0xf84920b846f8448001a00000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000"));

        let account = AccountVec::new(U256::from(100), 1, B256::ZERO, B256::ZERO);
        let node = Node::new_account_leaf(Nibbles::from_nibbles([0xa, 0xb]), account, None);
        let mut bytes = vec![];
        node.encode(&mut bytes);
        assert_eq!(bytes, hex!("0xf84b8220abb846f8440164a00000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000"));

        let account = AccountVec::new(U256::from(123456789), 999, B256::ZERO, B256::ZERO);
        let node = Node::new_account_leaf(
            Nibbles::from_nibbles([0xa, 0xb, 0xc, 0xd, 0xe]),
            account,
            None,
        );
        let mut bytes = vec![];
        node.encode(&mut bytes);
        assert_eq!(bytes, hex!("0xf852833abcdeb84cf84a8203e784075bcd15a00000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000"));

        let account = AccountVec::new(
            U256::from(10_000_000_000_000_000_000u64),
            0,
            KECCAK_EMPTY,
            EMPTY_ROOT_HASH,
        );
        let node = Node::new_account_leaf(
            Nibbles::unpack(hex!(
                "0x761d5c42184a02cc64585ed2ff339fc39a907e82731d70313c83d2212b2da36b"
            )),
            account,
            None,
        );
        let mut bytes = vec![];
        node.encode(&mut bytes);
        assert_eq!(bytes, hex!("0xf872a120761d5c42184a02cc64585ed2ff339fc39a907e82731d70313c83d2212b2da36bb84ef84c80888ac7230489e80000a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"));
        let rlp_encoded = node.rlp_encode();
        // hash prefixed with 0xa0 (length 32)
        assert_eq!(
            rlp_encoded.as_slice(),
            hex!("0xa0337e249c268401079fc728c58142710845805285dbc90e7c71bb1b79b9d7a745")
        );
    }

    #[test]
    fn test_branch_node_encode() {
        let mut node: Node<AccountVec> = Node::new_branch(Nibbles::new());
        node.set_child(
            0,
            Pointer::new(
                0.into(),
                RlpNode::word_rlp(&b256!(
                    "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
                )),
            ),
        );
        node.set_child(
            15,
            Pointer::new(
                15.into(),
                RlpNode::word_rlp(&b256!(
                    "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
                )),
            ),
        );
        let mut bytes = vec![];
        node.encode(&mut bytes);
        assert_eq!(bytes, hex!("0xf851a01234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef8080808080808080808080808080a0deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef80"));

        let mut node: Node<AccountVec> = Node::new_branch(Nibbles::new());
        node.set_child(
            3,
            Pointer::new(
                0.into(),
                RlpNode::word_rlp(&b256!(
                    "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
                )),
            ),
        );
        node.set_child(
            7,
            Pointer::new(
                15.into(),
                RlpNode::word_rlp(&b256!(
                    "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
                )),
            ),
        );
        node.set_child(
            13,
            Pointer::new(
                13.into(),
                RlpNode::word_rlp(&b256!(
                    "0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f"
                )),
            ),
        );
        let mut bytes = vec![];
        node.encode(&mut bytes);
        assert_eq!(bytes, hex!("0xf871808080a01234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef808080a0deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef8080808080a0f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f808080"));

        let mut node: Node<AccountVec> = Node::new_branch(Nibbles::from_nibbles([0x1, 0x2]));
        node.set_child(
            0,
            Pointer::new(
                0.into(),
                RlpNode::word_rlp(&b256!(
                    "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
                )),
            ),
        );
        node.set_child(
            15,
            Pointer::new(
                15.into(),
                RlpNode::word_rlp(&b256!(
                    "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
                )),
            ),
        );
        let mut bytes = vec![];
        node.encode(&mut bytes);
        assert_eq!(
            bytes,
            hex!("0xe4820012a07bd949f8cd65627b2b00e38e837d3d6136a9fd1599e3677a4b5a730e2176f67d")
        );

        let mut node: Node<AccountVec> =
            Node::new_branch(Nibbles::from_nibbles([0x7, 0x7, 0x7, 0x7, 0x7, 0x7, 0x7]));
        node.set_child(
            3,
            Pointer::new(
                0.into(),
                RlpNode::word_rlp(&b256!(
                    "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
                )),
            ),
        );
        node.set_child(
            7,
            Pointer::new(
                15.into(),
                RlpNode::word_rlp(&b256!(
                    "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
                )),
            ),
        );
        node.set_child(
            13,
            Pointer::new(
                13.into(),
                RlpNode::word_rlp(&b256!(
                    "0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f"
                )),
            ),
        );
        let encoded = encode(&node);
        node.encode(&mut bytes);
        assert_eq!(
            encoded,
            hex!(
                "0xe68417777777a0dea7c3591d20f8be14c2ae9448648a7c4f7e63f3bad1ae7bf750871a66d3b95b"
            )
        );

        let mut node: Node<AccountVec> = Node::new_branch(Nibbles::new());
        node.set_child(
            5,
            Pointer::new(
                5.into(),
                RlpNode::word_rlp(&b256!(
                    "0x18e3b46e84b35270116303fb2a33c853861d45d99da2d87117c2136f7edbd0b9"
                )),
            ),
        );
        node.set_child(
            7,
            Pointer::new(
                7.into(),
                RlpNode::word_rlp(&b256!(
                    "0x717aef38e7ba4a0ae477856a6e7f6ba8d4ee764c57908e6f22643a558db737ff"
                )),
            ),
        );
        let encoded = encode(&node);
        assert_eq!(
            encoded,
            hex!(
                "0xf8518080808080a018e3b46e84b35270116303fb2a33c853861d45d99da2d87117c2136f7edbd0b980a0717aef38e7ba4a0ae477856a6e7f6ba8d4ee764c57908e6f22643a558db737ff808080808080808080"
            )
        );
        let rlp_encoded = node.rlp_encode();
        // hash prefixed with 0xa0 (length 32)
        assert_eq!(
            rlp_encoded.as_slice(),
            hex!("0xa00d9348243d7357c491e6a61f4b1305e77dc6acacdb8cc708e662f6a9bab6ca02")
        );
    }

    #[test]
    fn test_branch_node_encode_decode() {
        let nibbles = Nibbles::from_nibbles([0x1, 0x2, 0x3, 0x4]);
        let mut node: Node<AccountVec> = Node::new_branch(nibbles);
        node.set_child(
            0,
            Pointer::new(
                0.into(),
                RlpNode::word_rlp(&b256!(
                    "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
                )),
            ),
        );
        node.set_child(
            1,
            Pointer::new(
                1.into(),
                RlpNode::word_rlp(&b256!(
                    "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
                )),
            ),
        );
        node.set_child(
            2,
            Pointer::new(
                2.into(),
                RlpNode::word_rlp(&b256!(
                    "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
                )),
            ),
        );
        assert_eq!(node.size(), 2 + 4 + 2 + 36 * 16);

        let x = node.serialize().unwrap();
        let y = Node::from_bytes(&x).unwrap();
        assert_eq!(node, y);
    }

    proptest! {
        #[test]
        fn fuzz_node_to_from_bytes(node: Node<AccountVec>) {
            let bytes = node.serialize().unwrap();
            let decoded = Node::from_bytes(&bytes).unwrap();
            assert_eq!(node, decoded);
        }

        #[test]
        fn fuzz_node_rlp_encode(node: Node<AccountVec>) {
            let mut bytes = vec![];
            node.encode(&mut bytes);
        }
    }
}
