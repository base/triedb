//! Node types for the trie database.
//!
//! A [Node] represents a single node in the Merkle Patricia Trie, which can be:
//! - An [AccountLeaf][NodeKind::AccountLeaf] storing account data (balance, nonce, code hash,
//!   storage root)
//! - A [StorageLeaf][NodeKind::StorageLeaf] storing a storage value
//! - A [Branch][NodeKind::Branch] with up to 16 children
//!
//! ## Module Organization
//!
//! - [`encoding`]: Binary serialization for page storage (Value trait impl)
//! - [`rlp`]: RLP encoding for state root computation (Encodable impl)
//! - [`arbitrary`]: Proptest strategies for fuzzing

mod arbitrary;
mod encoding;
mod rlp;

pub use rlp::{encode_account_leaf, encode_branch};

use crate::{account::Account, path::RawPath, pointer::Pointer};
use alloy_primitives::{StorageValue, B256};
use alloy_rlp::{decode_exact, encode_fixed_size, MaxEncodedLen};
use alloy_trie::{nodes::RlpNode, Nibbles, EMPTY_ROOT_HASH};
use arrayvec::ArrayVec;
use proptest_derive::Arbitrary;
use std::cmp::{max, min};

const MAX_PREFIX_LENGTH: usize = 64;

/// A node in the trie.
///
/// This may be an account leaf, a storage leaf, or a branch.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Node(Box<NodeInner>);

#[derive(Clone, PartialEq, Eq, Debug, Arbitrary)]
pub(crate) struct NodeInner {
    pub(crate) prefix: Nibbles,
    pub(crate) kind: NodeKind,
}

// Allow `large_enum_variant` because this enum is expected to only live inside a `Box`.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, PartialEq, Eq, Debug, Arbitrary)]
pub enum NodeKind {
    AccountLeaf {
        #[proptest(strategy = "arbitrary::arb_u64_rlp()")]
        nonce_rlp: ArrayVec<u8, 9>,
        #[proptest(strategy = "arbitrary::arb_u256_rlp()")]
        balance_rlp: ArrayVec<u8, 33>,
        code_hash: B256,
        storage_root: Option<Pointer>,
    },
    StorageLeaf {
        #[proptest(strategy = "arbitrary::arb_u256_rlp()")]
        value_rlp: ArrayVec<u8, 33>,
    },
    Branch {
        #[proptest(strategy = "arbitrary::arb_children()")]
        children: [Option<Pointer>; 16],
    },
}

#[derive(Debug)]
pub enum NodeError {
    ChildrenUnsupported,
    MaxPrefixLengthExceeded,
    NoValue,
}

impl Node {
    /// Creates a new account leaf or storage leaf [Node] from a [Nibbles] prefix and a [TrieValue].
    ///
    /// # Panics
    ///
    /// This function will panic if the provided prefix is greater than 64 nibbles long.
    pub fn new_leaf(prefix: &RawPath, value: &TrieValue) -> Result<Self, NodeError> {
        let prefix = prefix.try_into().map_err(|_| NodeError::MaxPrefixLengthExceeded)?;

        match value {
            TrieValue::Account(account) => Ok(Self::new_account_leaf(
                prefix,
                encode_fixed_size(&account.balance),
                encode_fixed_size(&account.nonce),
                account.code_hash,
                None,
            )),
            TrieValue::Storage(storage) => {
                Ok(Self::new_storage_leaf(prefix, encode_fixed_size(storage)))
            }
        }
    }

    fn new_account_leaf(
        prefix: Nibbles,
        balance_rlp: ArrayVec<u8, 33>,
        nonce_rlp: ArrayVec<u8, 9>,
        code_hash: B256,
        storage_root: Option<Pointer>,
    ) -> Self {
        Self::new(prefix, NodeKind::AccountLeaf { balance_rlp, nonce_rlp, code_hash, storage_root })
    }

    fn new_storage_leaf(prefix: Nibbles, value_rlp: ArrayVec<u8, 33>) -> Self {
        Self::new(prefix, NodeKind::StorageLeaf { value_rlp })
    }

    /// Creates a new branch [Node] from a [Nibbles] prefix.
    ///
    /// # Panics
    ///
    /// This function will panic if the provided prefix is greater than 64 nibbles long.
    pub fn new_branch(prefix: &RawPath) -> Result<Self, NodeError> {
        let prefix = prefix.try_into().map_err(|_| NodeError::MaxPrefixLengthExceeded)?;

        Ok(Self::new(prefix, NodeKind::Branch { children: [const { None }; 16] }))
    }

    pub(crate) fn new(prefix: Nibbles, kind: NodeKind) -> Self {
        Self(Box::new(NodeInner { prefix, kind }))
    }

    /// Returns the prefix of the [Node].
    pub const fn prefix(&self) -> &Nibbles {
        &self.0.prefix
    }

    /// Sets the prefix of the [Node].
    ///
    /// # Panics
    ///
    /// This function will panic if the provided prefix is greater than 64 nibbles long.
    pub fn set_prefix(&mut self, new_prefix: Nibbles) -> Result<(), NodeError> {
        if new_prefix.len() > MAX_PREFIX_LENGTH {
            return Err(NodeError::MaxPrefixLengthExceeded);
        }

        self.0.prefix = new_prefix;
        Ok(())
    }

    pub const fn kind(&self) -> &NodeKind {
        &self.0.kind
    }

    pub fn into_kind(self) -> NodeKind {
        self.0.kind
    }

    /// Returns whether the [Node] type supports children.
    pub const fn has_children(&self) -> bool {
        matches!(self.kind(), NodeKind::Branch { .. } | NodeKind::AccountLeaf { .. })
    }

    /// Returns whether the [Node] is an account leaf.
    pub const fn is_account_leaf(&self) -> bool {
        matches!(self.kind(), NodeKind::AccountLeaf { .. })
    }

    /// Returns whether the [Node] is a branch.
    pub const fn is_branch(&self) -> bool {
        matches!(self.kind(), NodeKind::Branch { .. })
    }

    /// Enumerates the children of the [Node].
    pub fn enumerate_children(&self) -> Result<Vec<(u8, &Pointer)>, NodeError> {
        match self.kind() {
            NodeKind::AccountLeaf { ref storage_root, .. } => {
                let children = [storage_root]
                    .iter()
                    .enumerate()
                    .filter_map(|(i, child)| child.as_ref().map(|child| (i as u8, child)))
                    .collect();

                Ok(children)
            }
            NodeKind::Branch { ref children } => {
                let children = children
                    .iter()
                    .enumerate()
                    .filter_map(|(i, child)| child.as_ref().map(|p| (i as u8, p)))
                    .collect();

                Ok(children)
            }
            _ => Err(NodeError::ChildrenUnsupported),
        }
    }

    /// Returns the child of the [Node] at the given index.
    pub fn child(&self, index: u8) -> Result<Option<&Pointer>, NodeError> {
        match self.kind() {
            NodeKind::Branch { ref children } => Ok(children[index as usize].as_ref()),
            _ => Err(NodeError::ChildrenUnsupported),
        }
    }

    /// Returns the direct child of the [Node].
    ///
    /// # Panics
    ///
    /// This function will panic if the [Node] is not an account leaf.
    pub fn direct_child(&self) -> Result<Option<&Pointer>, NodeError> {
        match self.kind() {
            NodeKind::AccountLeaf { ref storage_root, .. } => Ok(storage_root.as_ref()),
            _ => Err(NodeError::ChildrenUnsupported),
        }
    }

    /// Sets the child of the [Node] at the given index.
    ///
    /// # Panics
    ///
    /// This function will panic if the [Node] type does not support children.
    pub fn set_child(&mut self, index: u8, child: Pointer) -> Result<(), NodeError> {
        match self.0.kind {
            NodeKind::AccountLeaf { ref mut storage_root, .. } => {
                *storage_root = Some(child);
                Ok(())
            }
            NodeKind::Branch { ref mut children } => {
                children[index as usize] = Some(child);
                Ok(())
            }
            _ => Err(NodeError::ChildrenUnsupported),
        }
    }

    /// Removes the child of the [Node] at the given index.
    ///
    /// # Panics
    ///
    /// This function will panic if the [Node] type does not support children.
    pub fn remove_child(&mut self, index: u8) -> Result<(), NodeError> {
        match self.0.kind {
            NodeKind::AccountLeaf { ref mut storage_root, .. } => {
                *storage_root = None;
                Ok(())
            }
            NodeKind::Branch { ref mut children } => {
                children[index as usize] = None;
                Ok(())
            }
            _ => Err(NodeError::ChildrenUnsupported),
        }
    }

    /// Returns the value of the [Node].
    ///
    /// # Panics
    ///
    /// This function will panic if the [Node] is not a leaf.
    pub fn value(&self) -> Result<TrieValue, NodeError> {
        match self.kind() {
            NodeKind::StorageLeaf { ref value_rlp, .. } => {
                Ok(TrieValue::Storage(decode_exact(value_rlp).expect("invalid storage rlp")))
            }
            NodeKind::AccountLeaf {
                ref balance_rlp,
                ref nonce_rlp,
                ref code_hash,
                ref storage_root,
            } => Ok(TrieValue::Account(Account {
                balance: decode_exact(balance_rlp).expect("invalid balance rlp"),
                nonce: decode_exact(nonce_rlp).expect("invalid nonce rlp"),
                storage_root: storage_root
                    .as_ref()
                    .and_then(|p| p.rlp().as_hash())
                    .unwrap_or(EMPTY_ROOT_HASH),
                code_hash: *code_hash,
            })),
            _ => Err(NodeError::NoValue),
        }
    }

    /// Returns the embedded RLP encoding of the [Node].
    ///
    /// This will typically be a 33 byte prefixed keccak256 hash.
    pub fn to_rlp_node(&self) -> RlpNode {
        RlpNode::from_rlp(&self.rlp_encode())
    }

    /// Returns the RLP encoding of the [Node].
    pub fn rlp_encode(&self) -> ArrayVec<u8, MAX_RLP_ENCODED_LEN> {
        encode_fixed_size(self)
    }

    /// Returns the size of the [Node] if a new child were to be added.
    pub fn size_incr_with_new_child(&self) -> usize {
        match self.kind() {
            NodeKind::Branch { ref children } => {
                let (total_children, slot_size) = Self::children_slot_size(children);
                let next_total_children = min(total_children + 1, 16);
                let next_slot_size = max(next_total_children.next_power_of_two(), 2);
                (next_slot_size - slot_size) * 37
            }
            NodeKind::AccountLeaf { ref storage_root, .. } => {
                if storage_root.is_none() {
                    37
                } else {
                    0
                }
            }
            _ => 0,
        }
    }

    pub(crate) fn children_slot_size(children: &[Option<Pointer>]) -> (usize, usize) {
        // children is saved in a list of 2, 4, 8, 16 slots depending on the number of children
        const MIN_SLOT_SIZE: usize = 2;
        let total_children = children.iter().filter(|child| child.is_some()).count();
        let slot_size = max(total_children.next_power_of_two(), MIN_SLOT_SIZE);
        (total_children, slot_size)
    }
}

/// This is the maximum possible RLP-encoded length of a node.
///
/// This value is derived from the maximum possible length of a branch node, which is the largest
/// case. A branch node is encoded as a list of 17 elements, including 16 children and an empty
/// list. Each child is encoded with up to 33 bytes, and the empty list adds 1 byte. Another 3
/// bytes are required to encode the list itself. The total length is `3 + 16*33 + 1 = 532`.
pub(crate) const MAX_RLP_ENCODED_LEN: usize = 3 + 16 * 33 + 1;

unsafe impl MaxEncodedLen<MAX_RLP_ENCODED_LEN> for Node {}

/// The value stored in a [Node].
/// This can be either an [Account] or a [StorageValue].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrieValue {
    Account(Account),
    Storage(StorageValue),
}

impl From<Account> for TrieValue {
    fn from(val: Account) -> Self {
        TrieValue::Account(val)
    }
}

impl From<StorageValue> for TrieValue {
    fn from(val: StorageValue) -> Self {
        TrieValue::Storage(val)
    }
}

#[cfg(test)]
mod tests;
