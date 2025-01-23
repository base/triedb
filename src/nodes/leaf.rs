use alloy_primitives::B256;
use alloy_trie::{nodes::LeafNodeRef, Nibbles, nodes::RlpNode};
use std::sync::Arc;
use crate::value::Value;
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeafNode<V: Value> {
    pub prefix: Nibbles,
    pub value: Arc<V>,
}

impl<V: Value> LeafNode<V> {
    pub fn new(prefix: Nibbles, value: V) -> Self {
        Self { prefix, value: Arc::new(value) }
    }

    pub fn with_prefix(mut self, prefix: Nibbles) -> Self {
        self.prefix = prefix;
        self
    }

    pub fn with_value(mut self, value: V) -> Self {
        self.value = Arc::new(value);
        self
    }

    pub fn hash(&self) -> B256 {
        self.rlp().as_hash().unwrap()
    }

    fn rlp(&self) -> RlpNode {
        let mut rlp_vec = Vec::new();
        LeafNodeRef::new(&self.prefix, self.value.as_bytes().as_slice()).rlp(&mut rlp_vec)
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        // Calculate total size needed
        let prefix_bytes = self.prefix.to_vec();
        let value_bytes = self.value.as_bytes();
        let mut data = Vec::with_capacity(8 + prefix_bytes.len() + value_bytes.len());
        
        // Write prefix length
        data.extend_from_slice(&(prefix_bytes.len() as u64).to_le_bytes());
        // Write prefix
        data.extend_from_slice(&prefix_bytes);
        // Write value
        data.extend_from_slice(&value_bytes);
        
        data
    }

    pub fn from_bytes(data: &[u8]) -> Self {
        let prefix_len = u64::from_le_bytes(data[0..8].try_into().unwrap()) as usize;
        let prefix = Nibbles::from_nibbles(&data[8..8 + prefix_len]);
        let value = Arc::new(V::from_bytes(&data[8 + prefix_len..]));
        Self { prefix, value }
    }
}
