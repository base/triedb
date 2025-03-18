use std::cmp::{max, min};

use alloy_primitives::{hex, StorageValue, B256, U256};
use alloy_rlp::{
    decode_exact, encode_fixed_size, length_of_length, BufMut, Encodable, Header, MaxEncodedLen,
    EMPTY_STRING_CODE,
};
use alloy_trie::{
    nodes::{ExtensionNodeRef, LeafNodeRef, RlpNode},
    Nibbles, EMPTY_ROOT_HASH, KECCAK_EMPTY,
};
use arrayvec::ArrayVec;
use proptest::prelude::{any, prop, Strategy};
use proptest_derive::Arbitrary;

use crate::{
    account::Account,
    pointer::Pointer,
    storage::value::{self, Value},
};

// This is equivalent to RlpNode::word_rlp(&EMPTY_ROOT_HASH), and is used to encode the storage root
// of an account with no storage.
const EMPTY_ROOT_RLP: [u8; 33] =
    hex!("0xa056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421");

/// A node in the trie.
/// This may be an account leaf, a storage leaf, or a branch.
#[derive(Debug, Clone, PartialEq, Eq, Arbitrary)]
pub enum Node {
    AccountLeaf {
        prefix: Nibbles,
        #[proptest(strategy = "arb_u64_rlp()")]
        nonce_rlp: ArrayVec<u8, 9>,
        #[proptest(strategy = "arb_u256_rlp()")]
        balance_rlp: ArrayVec<u8, 33>,
        code_hash: B256,
        storage_root: Option<Pointer>,
    },
    StorageLeaf {
        prefix: Nibbles,
        #[proptest(strategy = "arb_u256_rlp()")]
        value_rlp: ArrayVec<u8, 33>,
    },
    Branch {
        prefix: Nibbles,
        #[proptest(strategy = "arb_children()")]
        children: [Option<Pointer>; 16],
    },
}

fn arb_u64_rlp() -> impl Strategy<Value = ArrayVec<u8, 9>> {
    any::<u64>().prop_map(|u| encode_fixed_size(&u)).boxed()
}

fn arb_u256_rlp() -> impl Strategy<Value = ArrayVec<u8, 33>> {
    any::<U256>().prop_map(|u| encode_fixed_size(&u)).boxed()
}

impl Node {
    /// Creates a new account leaf or storage leaf [Node] from a [Nibbles] prefix and a [TrieValue].
    ///
    /// # Panics
    ///
    /// This function will panic if the provided prefix is greater than 64 nibbles long.
    pub fn new_leaf(prefix: Nibbles, value: &TrieValue) -> Self {
        assert!(prefix.len() <= 64, "account and storage leaf prefix's must be at most 64 nibbles");
        match value {
            TrieValue::Account(account) => Node::new_account_leaf(
                prefix,
                encode_fixed_size(&account.balance),
                encode_fixed_size(&account.nonce),
                account.code_hash,
                None,
            ),
            TrieValue::Storage(storage) => {
                Node::new_storage_leaf(prefix, encode_fixed_size(storage))
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
        Self::AccountLeaf { prefix, balance_rlp, nonce_rlp, code_hash, storage_root }
    }

    fn new_storage_leaf(prefix: Nibbles, value_rlp: ArrayVec<u8, 33>) -> Self {
        Self::StorageLeaf { prefix, value_rlp }
    }

    /// Creates a new branch [Node] from a [Nibbles] prefix.
    ///
    /// # Panics
    ///
    /// This function will panic if the provided prefix is greater than 64 nibbles long.
    pub fn new_branch(prefix: Nibbles) -> Self {
        assert!(prefix.len() <= 64, "branch prefix's must be at most 64 nibbles");
        Self::Branch { prefix, children: [const { None }; 16] }
    }

    /// Returns the prefix of the [Node].
    pub fn prefix(&self) -> &Nibbles {
        match self {
            Self::StorageLeaf { prefix, .. } => prefix,
            Self::AccountLeaf { prefix, .. } => prefix,
            Self::Branch { prefix, .. } => prefix,
        }
    }

    /// Sets the prefix of the [Node].
    ///
    /// # Panics
    ///
    /// This function will panic if the provided prefix is greater than 64 nibbles long.
    pub fn set_prefix(&mut self, new_prefix: Nibbles) {
        assert!(new_prefix.len() <= 64, "prefix's must be at most 64 nibbles");
        match self {
            Self::StorageLeaf { prefix, .. } => *prefix = new_prefix,
            Self::AccountLeaf { prefix, .. } => *prefix = new_prefix,
            Self::Branch { prefix, .. } => *prefix = new_prefix,
        }
    }

    /// Returns whether the [Node] type supports children.
    pub fn has_children(&self) -> bool {
        matches!(self, Self::Branch { .. } | Self::AccountLeaf { .. })
    }

    /// Returns whether the [Node] is a branch.
    pub fn is_branch(&self) -> bool {
        matches!(self, Self::Branch { .. })
    }

    /// Returns whether the [Node] is a branch.
    pub fn is_account_leaf(&self) -> bool {
        matches!(self, Self::AccountLeaf { .. })
    }

    /// Enumerates the children of the [Node].
    ///
    /// # Panics
    ///
    /// This function will panic if the [Node] type does not support children.
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

    /// Returns the child of the [Node] at the given index.
    ///
    /// # Panics
    ///
    /// This function will panic if the [Node] is not a branch.
    pub fn child(&self, index: u8) -> Option<&Pointer> {
        match self {
            Self::Branch { children, .. } => children[index as usize].as_ref(),
            _ => panic!("cannot get child of leaf node"),
        }
    }

    /// Returns the direct child of the [Node].
    ///
    /// # Panics
    ///
    /// This function will panic if the [Node] is not an account leaf.
    pub fn direct_child(&self) -> Option<&Pointer> {
        match self {
            Self::AccountLeaf { storage_root, .. } => storage_root.as_ref(),
            _ => panic!("cannot get direct child of non-leaf node"),
        }
    }

    /// Sets the child of the [Node] at the given index.
    ///
    /// # Panics
    ///
    /// This function will panic if the [Node] type does not support children.
    pub fn set_child(&mut self, index: u8, child: Pointer) {
        match self {
            Self::AccountLeaf { storage_root, .. } => *storage_root = Some(child),
            Self::Branch { children, .. } => children[index as usize] = Some(child),
            _ => panic!("cannot set child of non-branch node"),
        }
    }

    /// Removes the child of the [Node] at the given index.
    ///
    /// # Panics
    ///
    /// This function will panic if the [Node] type does not support children.
    pub fn remove_child(&mut self, index: u8) {
        match self {
            Self::AccountLeaf { storage_root, .. } => *storage_root = None,
            Self::Branch { children, .. } => children[index as usize] = None,
            _ => panic!("cannot set child of non-branch node"),
        }
    }

    /// Returns the value of the [Node].
    ///
    /// # Panics
    ///
    /// This function will panic if the [Node] is not a leaf.
    pub fn value(&self) -> TrieValue {
        match self {
            Self::StorageLeaf { value_rlp, .. } => {
                TrieValue::Storage(decode_exact(value_rlp).expect("invalid storage rlp"))
            }
            Self::AccountLeaf { balance_rlp, nonce_rlp, code_hash, storage_root, .. } => {
                TrieValue::Account(Account {
                    balance: decode_exact(balance_rlp).expect("invalid balance rlp"),
                    nonce: decode_exact(nonce_rlp).expect("invalid nonce rlp"),
                    storage_root: storage_root
                        .as_ref()
                        .and_then(|p| p.rlp().as_hash())
                        .unwrap_or(EMPTY_ROOT_HASH),
                    code_hash: *code_hash,
                })
            }
            _ => panic!("cannot get value of non-leaf node"),
        }
    }

    /// Returns the RLP encoding of the [Node].
    /// This will typically be a 33 byte prefixed keccak256 hash.
    pub fn rlp_encode(&self) -> RlpNode {
        RlpNode::from_rlp(&encode_fixed_size(self))
    }

    /// Returns the size of the [Node] if a new child were to be added.
    pub fn size_incr_with_new_child(&self) -> usize {
        match self {
            Self::Branch { children, .. } => {
                let (total_children, slot_size) = Self::children_slot_size(children);
                let next_total_children = min(total_children + 1, 16);
                let next_slot_size = max(next_total_children.next_power_of_two(), 2);
                (next_slot_size - slot_size) * 37
            }
            Self::AccountLeaf { storage_root, .. } => {
                if storage_root.is_none() {
                    37
                } else {
                    0
                }
            }
            _ => 0,
        }
    }

    fn children_slot_size(children: &[Option<Pointer>]) -> (usize, usize) {
        // children is saved in a list of 2, 4, 8, 16 slots depending on the number of children
        const MIN_SLOT_SIZE: usize = 2;
        let total_children = children.iter().filter(|child| child.is_some()).count();
        let slot_size = max(total_children.next_power_of_two(), MIN_SLOT_SIZE);
        (total_children, slot_size)
    }
}

// This is the maximum possible RLP-encoded length of a node.
// This value is derived from the maximum possible length of a branch node, which is the largest
// case. A branch node is encoded as a list of 17 elements, including 16 children and an empty list.
// Each child is encoded with up to 33 bytes, and the empty list adds 1 byte.
// Another 3 bytes are required to encode the list itself.
// The total length is 3 + 16*33 + 1 = 532.
unsafe impl MaxEncodedLen<{ 3 + 16 * 33 + 1 }> for Node {}

impl Value for Node {
    fn size(&self) -> usize {
        match self {
            Self::StorageLeaf { prefix, value_rlp } => {
                let packed_prefix_length = (prefix.len() + 1) / 2;
                2 + packed_prefix_length + value_rlp.len() // 2 bytes for type and prefix length
            }
            Self::AccountLeaf { prefix, balance_rlp, nonce_rlp, storage_root, code_hash } => {
                let packed_prefix_length = (prefix.len() + 1) / 2;
                2 + packed_prefix_length
                    + balance_rlp.len()
                    + nonce_rlp.len()
                    + storage_root.is_some() as usize * 37
                    + (*code_hash != KECCAK_EMPTY) as usize * 32 // 2 bytes for flags and prefix
                                                                 // length
            }
            Self::Branch { prefix, children } => {
                let (_, children_slot_size) = Self::children_slot_size(children);

                let packed_prefix_length = (prefix.len() + 1) / 2;
                2 + packed_prefix_length + 2 + children_slot_size * 37 // 2 bytes for type and
                                                                       // prefix length, 2 for
                                                                       // bitmask, 37 for each child
                                                                       // pointer
            }
        }
    }

    fn serialize_into(&self, buf: &mut [u8]) -> value::Result<usize> {
        match self {
            Self::StorageLeaf { prefix, value_rlp } => {
                let prefix_length = prefix.len();
                let packed_prefix_length = (prefix.len() + 1) / 2;
                let total_size = 2 + packed_prefix_length + value_rlp.len();
                if buf.len() < total_size {
                    return Err(value::Error::InvalidEncoding);
                }

                buf[0] = 0; // StorageLeaf type
                buf[1] = prefix_length as u8;
                prefix.pack_to(buf[2..2 + packed_prefix_length].as_mut());
                buf[2 + packed_prefix_length..].copy_from_slice(value_rlp.as_slice());

                Ok(total_size)
            }
            Self::AccountLeaf { prefix, balance_rlp, nonce_rlp, code_hash, storage_root } => {
                let prefix_length = prefix.len();
                let packed_prefix_length = (prefix.len() + 1) / 2;
                let total_size = 2
                    + packed_prefix_length
                    + balance_rlp.len()
                    + nonce_rlp.len()
                    + storage_root.is_some() as usize * 37
                    + (*code_hash != KECCAK_EMPTY) as usize * 32;
                if buf.len() < total_size {
                    return Err(value::Error::InvalidEncoding);
                }

                let flags = 1
                    | ((storage_root.is_some() as u8) << 7)
                    | (((*code_hash != KECCAK_EMPTY) as u8) << 6);

                buf[0] = flags;
                buf[1] = prefix_length as u8;
                let mut offset = 2;
                prefix.pack_to(buf[offset..offset + packed_prefix_length].as_mut());
                offset += packed_prefix_length;
                buf[offset..offset + nonce_rlp.len()].copy_from_slice(nonce_rlp.as_slice());
                offset += nonce_rlp.len();
                buf[offset..offset + balance_rlp.len()].copy_from_slice(balance_rlp.as_slice());
                offset += balance_rlp.len();
                if *code_hash != KECCAK_EMPTY {
                    buf[offset..offset + 32].copy_from_slice(code_hash.as_slice());
                    offset += 32;
                }

                if let Some(storage_root) = storage_root {
                    // Serialize the pointer
                    offset += storage_root.serialize_into(&mut buf[offset..offset + 37])?;
                }

                Ok(offset)
            }
            Self::Branch { prefix, children } => {
                let (total_children, children_slot_size) = Self::children_slot_size(children);

                let prefix_length = prefix.len();
                let packed_prefix_length = (prefix_length + 1) / 2;
                let total_size = 2 + packed_prefix_length + 2 + children_slot_size * 37; // Type, prefix length, bitmask + children pointers

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
                for child in children.iter().flatten() {
                    offset += child.serialize_into(&mut buf[offset..offset + 37])?;
                }
                let padding_size = (children_slot_size - total_children) * 37;
                buf[offset..offset + padding_size].fill(0);
                offset += padding_size;

                Ok(offset)
            }
        }
    }

    fn from_bytes(bytes: &[u8]) -> value::Result<Self> {
        let flags = bytes[0];
        if flags == 0 {
            let prefix_length = bytes[1] as usize;
            let packed_prefix_length = (prefix_length + 1) / 2;
            let mut prefix = Nibbles::unpack(&bytes[2..2 + packed_prefix_length]);
            prefix.truncate(prefix_length);

            let offset = 2 + packed_prefix_length;

            let value_header = bytes[offset];
            let value_rlp = if value_header <= 128 {
                let mut value_rlp = ArrayVec::new();
                value_rlp.push(value_header);
                value_rlp
            } else {
                let value_len = value_header as usize - 128;
                ArrayVec::from_iter(bytes[offset..offset + value_len + 1].iter().copied())
            };

            Ok(Self::StorageLeaf { prefix, value_rlp })
        } else if flags & 1 == 1 {
            let has_storage = flags & 0b10000000 != 0;
            let has_code = flags & 0b01000000 != 0;
            let prefix_length = bytes[1] as usize;
            let packed_prefix_length = (prefix_length + 1) / 2;
            let mut prefix = Nibbles::unpack(&bytes[2..2 + packed_prefix_length]);
            prefix.truncate(prefix_length);

            let mut offset = 2 + packed_prefix_length;

            let nonce_header = bytes[offset];
            let (nonce_rlp, nonce_len) = if nonce_header <= 128 {
                let mut nonce_rlp = ArrayVec::new();
                nonce_rlp.push(nonce_header);
                (nonce_rlp, 1)
            } else {
                let nonce_len = nonce_header as usize - 128;
                let nonce_rlp =
                    ArrayVec::from_iter(bytes[offset..offset + nonce_len + 1].iter().copied());
                (nonce_rlp, nonce_len + 1)
            };
            offset += nonce_len;

            let balance_header = bytes[offset];
            let (balance_rlp, balance_len) = if balance_header <= 128 {
                let mut balance_rlp = ArrayVec::new();
                balance_rlp.push(balance_header);
                (balance_rlp, 1)
            } else {
                let balance_len = balance_header as usize - 128;
                let balance_rlp =
                    ArrayVec::from_iter(bytes[offset..offset + balance_len + 1].iter().copied());
                (balance_rlp, balance_len + 1)
            };
            offset += balance_len;

            let mut storage_root = None;
            let mut code_hash = KECCAK_EMPTY;

            if has_code {
                if bytes.len() < offset + 32 {
                    return Err(value::Error::InvalidEncoding);
                }
                code_hash = B256::from_slice(&bytes[offset..offset + 32]);
                offset += 32;
            }

            if has_storage {
                if bytes.len() < offset + 37 {
                    return Err(value::Error::InvalidEncoding);
                }
                storage_root = Some(Pointer::from_bytes(&bytes[offset..offset + 37])?);
            }

            Ok(Self::AccountLeaf { prefix, balance_rlp, nonce_rlp, code_hash, storage_root })
        } else if flags == 2 {
            let prefix_length = bytes[1] as usize;
            let packed_prefix_length = (prefix_length + 1) / 2;
            let mut prefix = Nibbles::unpack(&bytes[2..2 + packed_prefix_length]);
            prefix.truncate(prefix_length);
            let children_bitmask = u16::from_be_bytes(
                bytes[2 + packed_prefix_length..2 + packed_prefix_length + 2].try_into().unwrap(),
            );
            let mut children = [const { None }; 16];
            let mut block_count = 0;
            for (i, child) in children.iter_mut().enumerate() {
                if children_bitmask & (1 << (15 - i)) == 0 {
                    continue;
                }
                let child_offset = 4 + packed_prefix_length + block_count * 37;
                let child_bytes = &bytes[child_offset..child_offset + 37];
                *child = Some(Pointer::from_bytes(child_bytes)?);
                block_count += 1;
            }
            Ok(Self::Branch { prefix, children })
        } else {
            return Err(value::Error::InvalidEncoding);
        }
    }
}

impl Encodable for Node {
    fn encode(&self, out: &mut dyn BufMut) {
        match self {
            Self::StorageLeaf { prefix, value_rlp } => {
                LeafNodeRef { key: prefix, value: value_rlp }.encode(out);
            }
            Self::AccountLeaf { prefix, balance_rlp, nonce_rlp, code_hash, storage_root } => {
                let mut buf = [0u8; 110]; // max RLP length for an account: 2 bytes for list length, 9 for nonce, 33 for
                                          // balance, 33 for storage root, 33 for code hash
                let mut value_rlp = buf.as_mut();
                let storage_root_rlp =
                    storage_root.as_ref().map(|p| p.rlp().as_slice()).unwrap_or(&EMPTY_ROOT_RLP);
                let len = 2 + nonce_rlp.len() + balance_rlp.len() + storage_root_rlp.len() + 33;
                value_rlp.put_u8(0xf8);
                value_rlp.put_u8((len - 2) as u8);
                value_rlp.put_slice(nonce_rlp);
                value_rlp.put_slice(balance_rlp);
                value_rlp.put_slice(storage_root_rlp);
                value_rlp.put_u8(0xa0);
                value_rlp.put_slice(code_hash.as_slice());
                LeafNodeRef { key: prefix, value: &buf[..len] }.encode(out);
            }
            Self::Branch { prefix, children } => {
                if prefix.is_empty() {
                    encode_branch(children, out);
                } else {
                    let mut buf = [0u8; 3 + 33 * 16 + 1]; // max RLP length for a branch: 3 bytes for the list length, 33 bytes for each
                                                          // of the 16 children, 1 byte for the empty 17th slot
                    let mut branch_rlp = buf.as_mut();

                    let branch_rlp_length = encode_branch(children, &mut branch_rlp);

                    ExtensionNodeRef {
                        key: prefix,
                        child: &RlpNode::from_rlp(&buf[..branch_rlp_length]),
                    }
                    .encode(out);
                }
            }
        }
    }

    fn length(&self) -> usize {
        match self {
            Self::StorageLeaf { prefix, .. } => {
                // this just has to be an estimate for `Vec::with_capacity`
                prefix.len() + 32 + 10 // 10 is just a buffer
            }
            Self::AccountLeaf { prefix, .. } => {
                // this just has to be an estimate for `Vec::with_capacity`
                prefix.len() + 32 + 8 + 32 + 37 + 10 // 10 is just a buffer
            }
            Self::Branch { prefix, children } => {
                if prefix.is_empty() {
                    let mut payload_length = 1;
                    for child in children.iter() {
                        if let Some(child) = child {
                            payload_length += child.rlp().len();
                        } else {
                            payload_length += 1;
                        }
                    }
                    payload_length + length_of_length(payload_length)
                } else {
                    let mut encoded_key_len = prefix.len() / 2 + 1;
                    if encoded_key_len != 1 {
                        encoded_key_len += length_of_length(encoded_key_len);
                    }
                    let payload_length = encoded_key_len + 33;
                    payload_length + length_of_length(payload_length)
                }
            }
        }
    }
}

fn encode_branch(children: &[Option<Pointer>], out: &mut dyn BufMut) -> usize {
    // first encode the header
    let mut payload_length = 1;
    for child in children.iter() {
        if let Some(child) = child {
            payload_length += child.rlp().len();
        } else {
            payload_length += 1;
        }
    }
    Header { list: true, payload_length }.encode(out);
    // now encode the children
    for child in children.iter() {
        if let Some(child) = child {
            out.put_slice(child.rlp());
        } else {
            out.put_u8(EMPTY_STRING_CODE);
        }
    }
    // and encode the empty 17th slot
    out.put_u8(EMPTY_STRING_CODE);

    payload_length + length_of_length(payload_length)
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
mod tests {
    use alloy_primitives::{b256, hex, B256, U256};
    use alloy_rlp::encode;
    use alloy_trie::KECCAK_EMPTY;
    use proptest::prelude::*;

    use super::*;

    #[test]
    fn test_size_branch() {
        // 2 children, reserve 2 children slots
        let mut node = Node::new_branch(Nibbles::new());
        node.set_child(0, Pointer::new(42.into(), RlpNode::from_rlp(&encode(10u8))));
        node.set_child(11, Pointer::new(11.into(), RlpNode::from_rlp(&encode("foo"))));
        let size = node.size();
        assert_eq!(size, 2 + 2 + 37 * 2); // 2 bytes for type and prefix length, 2 for bitmask, 37 for each 2 children pointers

        // 3 children, reserve 4 children slots
        let mut node = Node::new_branch(Nibbles::new());
        for i in 0..3 {
            node.set_child(i, Pointer::new((i as u32).into(), RlpNode::from_rlp(&encode(i))));
        }

        let size = node.size();
        assert_eq!(size, 2 + 2 + 37 * 4); // 2 bytes for type and prefix length, 2 for bitmask, 37 for each 4 children pointers

        // 4 children, reserve 4 children slots
        let mut node = Node::new_branch(Nibbles::new());
        for i in 10..14 {
            node.set_child(i, Pointer::new((i as u32).into(), RlpNode::from_rlp(&encode(i))));
        }
        let size = node.size();
        assert_eq!(size, 2 + 2 + 37 * 4); // 2 bytes for type and prefix length, 2 for bitmask, 37 for each 4 children pointers

        // 5 children, reserve 8 children slots
        let mut node = Node::new_branch(Nibbles::new());
        for i in 11..16 {
            node.set_child(i, Pointer::new((i as u32).into(), RlpNode::from_rlp(&encode(i))));
        }
        let size = node.size();
        assert_eq!(size, 2 + 2 + 37 * 8); // 2 bytes for type and prefix length, 2 for bitmask, 37 for each 8 children pointers

        // 8 children, reserve 8 children slots
        let mut node = Node::new_branch(Nibbles::new());
        for i in 5..13 {
            node.set_child(i, Pointer::new((i as u32).into(), RlpNode::from_rlp(&encode(i))));
        }
        let size = node.size();
        assert_eq!(size, 2 + 2 + 37 * 8); // 2 bytes for type and prefix length, 2 for bitmask, 37 for each 8 children pointers

        // 9 children, reserve 16 children slots
        let mut node = Node::new_branch(Nibbles::new());
        for i in 3..12 {
            node.set_child(i, Pointer::new((i as u32).into(), RlpNode::from_rlp(&encode(i))));
        }
        let size = node.size();
        assert_eq!(size, 2 + 2 + 37 * 16); // 2 bytes for type and prefix length, 2 for bitmask, 37
                                           // for each 16 children pointers
    }

    #[test]
    fn test_storage_leaf_node_serialize() {
        let node = Node::new_leaf(
            Nibbles::from_nibbles([0xa, 0xb]),
            &TrieValue::Storage(StorageValue::from_be_slice(&[4, 5, 6])),
        );
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x0002ab83040506"));

        let node = Node::new_leaf(
            Nibbles::from_nibbles([0xa, 0xb, 0xc]),
            &TrieValue::Storage(StorageValue::from_be_slice(&[4, 5, 6, 7])),
        );
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x0003abc08404050607"));

        let node = Node::new_leaf(
            Nibbles::new(),
            &TrieValue::Storage(StorageValue::from_be_slice(&[255, 255, 255, 255])),
        );
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x000084ffffffff"));

        let node = Node::new_leaf(Nibbles::new(), &TrieValue::Storage(StorageValue::from(0)));
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x000080"));

        let node = Node::new_leaf(
            Nibbles::from_nibbles(hex!(
                "0x000102030405060708090a0b0c0d0e0f000102030405060708090a0b0c0d0e0f"
            )),
            &TrieValue::Storage(StorageValue::from(U256::MAX)),
        );
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x00200123456789abcdef0123456789abcdefa0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"));
    }

    #[test]
    fn test_account_leaf_node_serialize() {
        let node = Node::new_leaf(
            Nibbles::from_nibbles([0xa, 0xb]),
            &TrieValue::Account(Account::new(
                0,
                U256::from_be_slice(&[4, 5, 6]),
                EMPTY_ROOT_HASH,
                KECCAK_EMPTY,
            )),
        );
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x0102ab8083040506"));

        let node = Node::new_leaf(
            Nibbles::from_nibbles([0xa, 0xb, 0xc]),
            &TrieValue::Account(Account::new(
                0,
                U256::from_be_slice(&[4, 5, 6, 7]),
                EMPTY_ROOT_HASH,
                KECCAK_EMPTY,
            )),
        );
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x0103abc0808404050607"));

        let node = Node::new_leaf(
            Nibbles::new(),
            &TrieValue::Account(Account::new(
                0,
                U256::from_be_slice(&[0xf, 0xf, 0xf, 0xf]),
                EMPTY_ROOT_HASH,
                b256!("0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"),
            )),
        );
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0x410080840f0f0f0fdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"));

        let mut node = Node::new_leaf(
            Nibbles::new(),
            &TrieValue::Account(Account::new(
                0,
                U256::from_be_slice(&[0xf, 0xf, 0xf, 0xf]),
                EMPTY_ROOT_HASH,
                b256!("0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"),
            )),
        );
        node.set_child(
            0,
            Pointer::new(
                42.into(),
                RlpNode::word_rlp(&b256!(
                    "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
                )),
            ),
        );
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes, hex!("0xc10080840f0f0f0fdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef0000002aa01234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"));
    }

    #[test]
    fn test_branch_node_serialize() {
        let mut node: Node = Node::new_branch(Nibbles::new());
        let hash1 = b256!("0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef");
        let hash2 = b256!("0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
        node.set_child(0, Pointer::new(42.into(), RlpNode::word_rlp(&hash1)));
        node.set_child(11, Pointer::new(43.into(), RlpNode::word_rlp(&hash2)));
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes.len(), 2 + 2 + 37 * 2);
        // branch, no prefix
        let mut expected = Vec::from([2, 0]);
        // children bitmask (10000000 00010000)
        expected.extend([128, 16]);
        // child 0
        expected.extend([0, 0, 0, 42, 160]);
        expected.extend(hash1.as_slice());
        // child 11
        expected.extend([0, 0, 0, 43, 160]);
        expected.extend(hash2.as_slice());
        // children 12-15
        assert_eq!(bytes, expected);

        let mut node: Node = Node::new_branch(Nibbles::from_nibbles([0xa, 0xb, 0xc, 0xd, 0xe]));
        let hash1 = b256!("0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef");
        let hash2 = b256!("0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
        let hash3 = b256!("0x1111111111111111111111111111111111111111111111111111111111111111");
        node.set_child(2, Pointer::new(100.into(), RlpNode::word_rlp(&hash1)));
        node.set_child(3, Pointer::new(200.into(), RlpNode::word_rlp(&hash2)));
        node.set_child(15, Pointer::new(210.into(), RlpNode::word_rlp(&hash3)));
        let bytes = node.serialize().unwrap();
        assert_eq!(bytes.len(), 2 + 3 + 2 + 37 * 4);
        // branch, length, prefix
        let mut expected = Vec::from([2, 5, 171, 205, 224]);
        // children bitmask (00110000 00000001)
        expected.extend([48, 1]);
        // child 2
        expected.extend([0, 0, 0, 100, 160]);
        expected.extend(hash1.as_slice());
        // child 3
        expected.extend([0, 0, 0, 200, 160]);
        expected.extend(hash2.as_slice());
        // child 15
        expected.extend([0, 0, 0, 210, 160]);
        expected.extend(hash3.as_slice());
        // remaining empty slot
        expected.extend([0; 37]);
        assert_eq!(bytes, expected);

        let mut node: Node = Node::new_branch(Nibbles::from_nibbles([0x0, 0x0]));
        let v1 = encode(1u8);
        let v2 = encode("hello world");
        node.set_child(1, Pointer::new(99999.into(), RlpNode::from_rlp(&v1)));
        node.set_child(2, Pointer::new(8675309.into(), RlpNode::from_rlp(&v2)));
        let bytes = node.serialize().unwrap();

        // branch, length, prefix
        let mut expected = Vec::from([2, 2, 0]);
        // children bitmask (01100000 00000000)
        expected.extend([96, 0]);
        // child 1
        expected.extend([0, 1, 134, 159]);
        expected.extend(v1);
        expected.extend([0; 32]);
        // child 2
        expected.extend([0, 132, 95, 237]);
        expected.extend(v2);
        expected.extend([0; 21]);
        assert_eq!(bytes, expected);
    }

    #[test]
    fn test_leaf_node_encode() {
        let node = Node::new_leaf(
            Nibbles::new(),
            &TrieValue::Account(Account::new(0, U256::from(1), B256::ZERO, B256::ZERO)),
        );
        let mut bytes = vec![];
        node.encode(&mut bytes);
        assert_eq!(bytes, hex!("0xf84920b846f8448001a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a00000000000000000000000000000000000000000000000000000000000000000"));

        let node = Node::new_leaf(
            Nibbles::from_nibbles([0xa, 0xb]),
            &TrieValue::Account(Account::new(1, U256::from(100), B256::ZERO, B256::ZERO)),
        );
        let mut bytes = vec![];
        node.encode(&mut bytes);
        assert_eq!(bytes, hex!("0xf84b8220abb846f8440164a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a00000000000000000000000000000000000000000000000000000000000000000"));

        let node = Node::new_leaf(
            Nibbles::from_nibbles([0xa, 0xb, 0xc, 0xd, 0xe]),
            &TrieValue::Account(Account::new(999, U256::from(123456789), B256::ZERO, B256::ZERO)),
        );
        let mut bytes = vec![];
        node.encode(&mut bytes);
        assert_eq!(bytes, hex!("0xf852833abcdeb84cf84a8203e784075bcd15a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a00000000000000000000000000000000000000000000000000000000000000000"));

        let node = Node::new_leaf(
            Nibbles::unpack(hex!(
                "0x761d5c42184a02cc64585ed2ff339fc39a907e82731d70313c83d2212b2da36b"
            )),
            &TrieValue::Account(Account::new(
                0,
                U256::from(10_000_000_000_000_000_000u64),
                EMPTY_ROOT_HASH,
                KECCAK_EMPTY,
            )),
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
        let mut node = Node::new_branch(Nibbles::new());
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

        let mut node = Node::new_branch(Nibbles::new());
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

        let mut node = Node::new_branch(Nibbles::from_nibbles([0x1, 0x2]));
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

        let mut node = Node::new_branch(Nibbles::from_nibbles([0x7, 0x7, 0x7, 0x7, 0x7, 0x7, 0x7]));
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

        let mut node = Node::new_branch(Nibbles::new());
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

    proptest! {
        #[test]
        fn fuzz_node_to_from_bytes(node: Node) {
            let bytes = node.serialize().unwrap();
            let decoded = Node::from_bytes(&bytes).unwrap();
            assert_eq!(node, decoded);
        }

        #[test]
        fn fuzz_node_rlp_encode(node: Node) {
            node.rlp_encode();
        }
    }
}
