use alloy_rlp::{encode, BufMut, Encodable};
use alloy_trie::{
    nodes::{BranchNode, ExtensionNodeRef, LeafNodeRef, RlpNode},
    Nibbles, TrieMask,
};

use crate::{
    account::AccountVec,
    pointer::Pointer,
    storage::value::{self, Value},
};

#[derive(Debug)]
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
        assert_eq!(
            prefix.len() <= 64,
            true,
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
        match self {
            Self::AccountLeaf { .. } => true,
            Self::Branch { .. } => true,
            _ => false,
        }
    }

    pub fn is_branch(&self) -> bool {
        match self {
            Self::Branch { .. } => true,
            _ => false,
        }
    }

    pub fn enumerate_children(&self) -> Vec<(u8, &Pointer)> {
        match self {
            Self::AccountLeaf { storage_root, .. } => vec![storage_root]
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

    pub fn to_value(self) -> V {
        match self {
            Self::AccountLeaf { value, .. } => value,
            Self::StorageLeaf { value, .. } => value,
            _ => panic!("cannot get value of non-leaf node"),
        }
    }
}

impl<V: Value + Encodable> Node<V> {
    pub fn rlp_encode(&self) -> RlpNode {
        RlpNode::from_rlp(&encode(&self))
    }
}

impl<V: Value> Value for Node<V> {
    fn to_bytes(&self) -> Vec<u8> {
        match self {
            Self::StorageLeaf { prefix, value } => {
                let prefix_length = prefix.len();
                let value_bytes = value.to_bytes();
                let mut data = vec![0; prefix_length + value_bytes.len() + 2];
                data[0] = 0; // first byte 0 signifies a StorageLeaf
                data[1] = prefix_length as u8;
                data[2..2 + prefix_length].copy_from_slice(prefix.as_slice());
                data[prefix_length + 2..].copy_from_slice(&value_bytes);
                data
            }
            Self::AccountLeaf {
                prefix,
                value,
                storage_root,
            } => {
                let prefix_length = prefix.len();
                let value_bytes = value.to_bytes();
                let mut data = vec![0; prefix_length + 37 + value_bytes.len() + 2];
                data[0] = 1; // first byte 1 signifies a AccountLeaf
                data[1] = prefix_length as u8;
                data[2..2 + prefix_length].copy_from_slice(prefix.as_slice());
                if let Some(storage) = storage_root {
                    data[prefix_length + 2..prefix_length + 2 + 37]
                        .copy_from_slice(&storage.to_bytes());
                } else {
                    data[prefix_length + 2..prefix_length + 2 + 37].copy_from_slice(&[0; 37]);
                };

                data[prefix_length + 2 + 37..].copy_from_slice(&value_bytes);
                data
            }
            Self::Branch { prefix, children } => {
                let prefix_length = prefix.len();
                let mut data = vec![0; prefix_length + 4];
                data[0] = 2; // first byte 2 signifies a Branch
                data[1] = prefix_length as u8;
                data[2..2 + prefix_length].copy_from_slice(prefix.as_slice());
                let children_bitmask = children
                    .iter()
                    .enumerate()
                    .map(|(idx, child)| (child.is_some() as u16) << (15 - idx))
                    .sum::<u16>();
                data[prefix_length + 2..prefix_length + 2 + 2]
                    .copy_from_slice(&children_bitmask.to_be_bytes());
                for child in children.into_iter() {
                    if let Some(child) = child {
                        data.extend_from_slice(&child.to_bytes());
                    } else {
                        data.extend_from_slice(&[0; 37]);
                    }
                }
                data
            }
        }
    }

    fn from_bytes(bytes: &[u8]) -> value::Result<Self> {
        let first_byte = bytes[0];
        if first_byte == 0 {
            let prefix_length = bytes[1] as usize;
            let prefix = Nibbles::from_nibbles(&bytes[2..2 + prefix_length]);
            let value = V::from_bytes(&bytes[prefix_length + 2..])?;
            Ok(Self::StorageLeaf { prefix, value })
        } else if first_byte == 1 {
            let prefix_length = bytes[1] as usize;
            let prefix = Nibbles::from_nibbles(&bytes[2..2 + prefix_length]);
            let storage_root_bytes = &bytes[prefix_length + 2..prefix_length + 2 + 37];
            let value = V::from_bytes(&bytes[prefix_length + 2 + 37..])?;

            let storage_root: Option<Pointer>;
            if storage_root_bytes == [0; 37] {
                storage_root = None
            } else {
                storage_root = Some(Pointer::from_bytes(storage_root_bytes)?)
            }

            Ok(Self::AccountLeaf {
                prefix,
                value,
                storage_root,
            })
        } else {
            let prefix_length = bytes[1] as usize;
            let prefix = Nibbles::from_nibbles(&bytes[2..2 + prefix_length]);
            let children_bitmask = u16::from_be_bytes(
                bytes[prefix_length + 2..prefix_length + 2 + 2]
                    .try_into()
                    .unwrap(),
            );
            let mut children = [const { None }; 16];
            for (i, child) in children.iter_mut().enumerate() {
                if children_bitmask & (1 << (15 - i)) == 0 {
                    continue;
                }
                let child_offset = 4 + prefix_length + i * 37;
                let child_bytes = bytes[child_offset..child_offset + 37].to_vec();
                *child = Some(Pointer::from_bytes(&child_bytes)?);
            }
            Ok(Self::Branch { prefix, children })
        }
    }
}

impl<V: Value + Encodable> Encodable for Node<V> {
    fn encode(&self, out: &mut dyn BufMut) {
        match self {
            Self::StorageLeaf { prefix, value } => {
                let value_rlp = encode(&value);
                LeafNodeRef {
                    key: prefix,
                    value: &value_rlp,
                }
                .encode(out);
            }
            Self::AccountLeaf {
                prefix,
                value,
                storage_root,
            } => {
                let value_rlp = encode(&value);
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
}

#[cfg(test)]
mod tests {
    use alloy_primitives::{b256, hex, B256, U256};
    use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};

    use crate::account::AccountVec;

    use super::*;

    #[test]
    fn test_storage_leaf_node_to_bytes() {
        let node = Node::new_storage_leaf(Nibbles::from_nibbles([0xa, 0xb]), vec![4, 5, 6]);
        let bytes = node.to_bytes();
        assert_eq!(bytes, hex!("00020a0b040506"));

        let node = Node::new_storage_leaf(Nibbles::from_nibbles([0xa, 0xb, 0xc]), vec![4, 5, 6, 7]);
        let bytes = node.to_bytes();
        assert_eq!(bytes, hex!("00030a0b0c04050607"));

        let node = Node::new_storage_leaf(Nibbles::new(), vec![0xf, 0xf, 0xf, 0xf]);
        let bytes = node.to_bytes();
        assert_eq!(bytes, hex!("00000f0f0f0f"));
    }

    #[test]
    fn test_account_leaf_node_to_bytes() {
        let node = Node::new_account_leaf(Nibbles::from_nibbles([0xa, 0xb]), vec![4, 5, 6], None);
        let bytes = node.to_bytes();
        assert_eq!(bytes, hex!("01020a0b00000000000000000000000000000000000000000000000000000000000000000000000000040506"));

        let node = Node::new_account_leaf(
            Nibbles::from_nibbles([0xa, 0xb, 0xc]),
            vec![4, 5, 6, 7],
            None,
        );
        let bytes = node.to_bytes();
        assert_eq!(bytes, hex!("01030a0b0c0000000000000000000000000000000000000000000000000000000000000000000000000004050607"));

        let node = Node::new_account_leaf(Nibbles::new(), vec![0xf, 0xf, 0xf, 0xf], None);
        let bytes = node.to_bytes();
        assert_eq!(bytes, hex!("0100000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f"));
    }

    #[test]
    fn test_branch_node_to_bytes() {
        let mut node: Node<Vec<u8>> = Node::new_branch(Nibbles::new());
        let hash1 = b256!("0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef");
        let hash2 = b256!("0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
        node.set_child(0, Pointer::new(42.into(), RlpNode::word_rlp(&hash1)));
        node.set_child(11, Pointer::new(11.into(), RlpNode::word_rlp(&hash2)));
        let bytes = node.to_bytes();
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
        let bytes = node.to_bytes();
        // branch, length, prefix
        let mut expected = Vec::from([2, 5, 10, 11, 12, 13, 14]);
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
        let bytes = node.to_bytes();

        // branch, length, prefix
        let mut expected = Vec::from([2, 2, 0, 0]);
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
}
