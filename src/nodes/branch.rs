use alloy_trie::Nibbles;
use crate::nodes::reference::NodeReference;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BranchNode {
    pub prefix: Nibbles,
    pub children: [Option<NodeReference>; 16],
}

impl BranchNode {
    pub fn new(prefix: Nibbles, children: [Option<NodeReference>; 16]) -> Self {
        Self { prefix, children }
    }

    pub fn with_prefix(mut self, prefix: Nibbles) -> Self {
        self.prefix = prefix;
        self
    }

    pub fn num_children(&self) -> usize {
        self.children.iter().filter(|child| child.is_some()).count()
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        let prefix_bytes = self.prefix.to_vec();
        let prefix_len = prefix_bytes.len();
        
        // Calculate total size: 8 bytes for prefix length + prefix bytes + (16 * 8) bytes for children
        let mut data = Vec::with_capacity(8 + prefix_len + 16 * 8);
        
        // Store prefix length
        data.extend_from_slice(&(prefix_len as u64).to_le_bytes());
        // Store prefix bytes
        data.extend_from_slice(&prefix_bytes);
        
        // Store children
        for child in &self.children {
            match child {
                Some(child) => data.extend_from_slice(&child.as_bytes()),
                None => data.extend_from_slice(&[255u8; 8]),
            }
        }
        
        data
    }

    pub fn from_bytes(data: &[u8]) -> Self {
        let prefix_len = u64::from_le_bytes(data[0..8].try_into().unwrap()) as usize;
        let prefix = Nibbles::from_nibbles(&data[8..8 + prefix_len]);
        
        let mut children = [const {None}; 16];
        let children_start = 8 + prefix_len;

        let mut child_start = children_start;
        for i in 0..16 {
            let first_byte = data[child_start];
            if first_byte == 255 {
                child_start += 8;
                continue;
            }
            let sixteen_bytes = &data[child_start..child_start + 16];
            children[i] = Some(NodeReference::from_bytes(sixteen_bytes));
            child_start += 16;
        }
        Self { prefix, children }
    }
}