use alloy_trie::Nibbles;

use crate::{
    pointer::Pointer,
    storage::value::{self, Value},
};

#[derive(Debug)]
pub enum Node {
    Leaf {
        prefix: Nibbles,
        value: Vec<u8>,
    },
    Branch {
        prefix: Nibbles,
        children: [Option<Pointer>; 16],
    },
}

#[derive(Debug, PartialEq, Eq)]
enum NodeType {
    Leaf,
    Branch,
}

impl Node {
    pub fn new_leaf(prefix: Nibbles, value: &[u8]) -> Self {
        Self::Leaf {
            prefix,
            value: value.to_vec(),
        }
    }

    pub fn new_branch(prefix: Nibbles) -> Self {
        Self::Branch {
            prefix,
            children: [const { None }; 16],
        }
    }

    pub fn prefix(&self) -> &Nibbles {
        match self {
            Self::Leaf { prefix, .. } => prefix,
            Self::Branch { prefix, .. } => prefix,
        }
    }

    pub fn set_prefix(&mut self, new_prefix: Nibbles) {
        match self {
            Self::Leaf { prefix, .. } => *prefix = new_prefix,
            Self::Branch { prefix, .. } => *prefix = new_prefix,
        }
    }

    pub fn child(&self, index: u8) -> Option<&Pointer> {
        match self {
            Self::Branch { children, .. } => children[index as usize].as_ref(),
            _ => panic!("cannot get child of leaf node"),
        }
    }

    pub fn set_child(&mut self, index: u8, child: Pointer) {
        match self {
            Self::Branch { children, .. } => children[index as usize] = Some(child),
            _ => panic!("cannot set child of non-branch node"),
        }
    }

    pub fn value(&self) -> Option<&[u8]> {
        match self {
            Self::Leaf { value, .. } => Some(value),
            _ => panic!("cannot get value of non-leaf node"),
        }
    }
}

impl Value for Node {
    fn to_bytes(self) -> Vec<u8> {
        match self {
            Self::Leaf { prefix, value, .. } => {
                let prefix_length = prefix.len();
                let mut data = vec![0; prefix_length + value.len() + 1];
                data[0] = prefix_length as u8;
                data[1..=prefix_length].copy_from_slice(prefix.as_slice());
                data[prefix_length + 1..].copy_from_slice(&value);
                data
            }
            Self::Branch { prefix, children } => {
                let prefix_length = prefix.len();
                let mut data = vec![0; prefix_length + 3];
                data[0] = prefix_length as u8 | 0b1000_0000;
                data[1..=prefix_length].copy_from_slice(prefix.as_slice());
                let children_bitmask = children
                    .iter()
                    .enumerate()
                    .map(|(idx, child)| (child.is_some() as u16) << idx)
                    .sum::<u16>();
                data[prefix_length + 1..prefix_length + 3]
                    .copy_from_slice(&children_bitmask.to_le_bytes());
                for child in children.into_iter() {
                    if let Some(child) = child {
                        data.extend_from_slice(&child.to_bytes());
                    } else {
                        data.extend_from_slice(&[0; 36]);
                    }
                }
                data
            }
        }
    }

    fn from_bytes(bytes: &[u8]) -> value::Result<Self> {
        let first_byte = bytes[0];
        if first_byte & 0b1000_0000 == 0 {
            let prefix_length = first_byte as usize & 0b0111_1111;
            let prefix = Nibbles::from_nibbles(&bytes[1..=prefix_length]);
            let value = bytes[prefix_length + 1..].to_vec();
            Ok(Self::Leaf { prefix, value })
        } else {
            let prefix_length = first_byte as usize & 0b0111_1111;
            let prefix = Nibbles::from_nibbles(&bytes[1..=prefix_length]);
            let children_bitmask = u16::from_le_bytes(
                bytes[prefix_length + 1..prefix_length + 3]
                    .try_into()
                    .unwrap(),
            );
            let mut children = [const { None }; 16];
            for (i, child) in children.iter_mut().enumerate() {
                if children_bitmask & (1 << i) == 0 {
                    continue;
                }
                let child_offset = 3 + prefix_length + i * 36;
                let child_bytes = bytes[child_offset..child_offset + 36].to_vec();
                *child = Some(Pointer::from_bytes(&child_bytes)?);
            }
            Ok(Self::Branch { prefix, children })
        }
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::hex;

    use super::*;

    #[test]
    fn test_leaf_node_to_bytes() {
        let node = Node::new_leaf(Nibbles::from_nibbles([0xa, 0xb]), &[4, 5, 6]);
        let bytes = node.to_bytes();
        assert_eq!(bytes, hex!("020a0b040506"));

        let node = Node::new_leaf(Nibbles::from_nibbles([0xa, 0xb, 0xc]), &[4, 5, 6, 7]);
        let bytes = node.to_bytes();
        assert_eq!(bytes, hex!("030a0b0c04050607"));

        let node = Node::new_leaf(Nibbles::new(), &[0xf, 0xf, 0xf, 0xf]);
        let bytes = node.to_bytes();
        assert_eq!(bytes, hex!("000f0f0f0f"));
    }

    #[test]
    fn test_branch_node_to_bytes() {
        let node = Node::new_branch(Nibbles::from_nibbles([0xa, 0xb]));
        let bytes = node.to_bytes();
        let mut expected = Vec::from(hex!("820a0b"));
        expected.extend(vec![0; 36 * 16 + 2]);
        assert_eq!(bytes, expected);

        let mut node = Node::new_branch(Nibbles::from_nibbles([0xa, 0xb]));
        node.set_child(0, Pointer::new_unhashed(7.into()));
        let bytes = node.to_bytes();
        let mut expected = Vec::from(hex!("820a0b"));
        expected.extend([1, 0, 0, 0, 0, 7]);
        expected.extend(vec![0; 36 * 16 - 4]);
        assert_eq!(bytes, expected);
    }
}
