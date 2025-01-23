use alloy_trie::Nibbles;
use crate::nodes::reference::NodeReference;

const BRANCHING_FACTOR: usize = 16;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BranchNode {
    pub prefix: Nibbles,
    children: [Option<NodeReference>; BRANCHING_FACTOR],
}

impl BranchNode {
    pub fn new(prefix: Nibbles) -> Self {
        Self { prefix, children: [const { None }; BRANCHING_FACTOR] }
    }

    pub fn new_with_children(prefix: Nibbles, children: [Option<NodeReference>; BRANCHING_FACTOR]) -> Self {
        Self { prefix, children }
    }

    pub fn with_prefix(mut self, prefix: Nibbles) -> Self {
        self.prefix = prefix;
        self
    }

    pub fn num_children(&self) -> usize {
        self.children.iter().filter(|child| child.is_some()).count()
    }

    pub fn set_child(&mut self, index: u8, child: Option<NodeReference>) {
        self.children[index as usize] = child;
    }

    pub fn get_child(&self, index: u8) -> Option<&NodeReference> {
        self.children[index as usize].as_ref()
    }

    pub fn children(&self) -> impl Iterator<Item = Option<&NodeReference>> {
        self.children.iter().map(|child| child.as_ref())
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        let prefix_bytes = self.prefix.to_vec();
        let prefix_len = prefix_bytes.len();
        
        // Calculate total size: 8 bytes for prefix length + prefix bytes + (16 * 37) bytes for children
        let mut data = Vec::with_capacity(8 + prefix_len + BRANCHING_FACTOR * 37);
        
        // Store prefix length
        data.extend_from_slice(&(prefix_len as u64).to_le_bytes());
        // Store prefix bytes
        data.extend_from_slice(&prefix_bytes);
        
        // Store children
        for child in &self.children {
            match child {
                Some(child) => data.extend_from_slice(&child.as_bytes()),
                None => data.extend_from_slice(&NodeReference::null().as_bytes()),
            }
        }
        
        data
    }

    pub fn from_bytes(data: &[u8]) -> Self {
        let prefix_len = u64::from_le_bytes(data[0..8].try_into().unwrap()) as usize;
        let prefix = Nibbles::from_nibbles(&data[8..8 + prefix_len]);
        
        let mut children = [const {None}; BRANCHING_FACTOR];
        let children_start = 8 + prefix_len;

        for i in 0..BRANCHING_FACTOR {
            let child_start = children_start + i * 37;
            let reference = NodeReference::from_bytes(&data[child_start..child_start + 37]);
            if reference.is_null() {
                continue;
            }
            children[i] = Some(reference);
        }

        Self { prefix, children }
    }
}
