//! RLP encoding for trie nodes.
//!
//! This module implements the [Encodable] trait for [Node], which defines how nodes
//! are encoded to RLP format for Merkle Patricia Trie state root computation.
//!
//! ## Encoding Formats
//!
//! - **Leaf nodes**: Encoded as `[key, value]` using compact hex encoding
//! - **Extension nodes**: Encoded as `[key, child_hash]` for branches with prefixes
//! - **Branch nodes**: Encoded as `[child0, ..., child15, value]` (17 elements)

use super::{Node, NodeKind};
use crate::pointer::Pointer;
use alloy_primitives::B256;
use alloy_rlp::{length_of_length, BufMut, Encodable, Header, EMPTY_STRING_CODE};
use alloy_trie::{
    nodes::{ExtensionNodeRef, LeafNodeRef, RlpNode},
    EMPTY_ROOT_HASH,
};
use arrayvec::ArrayVec;

impl Encodable for Node {
    fn encode(&self, out: &mut dyn BufMut) {
        let prefix = self.prefix();
        match self.kind() {
            NodeKind::StorageLeaf { ref value_rlp } => {
                LeafNodeRef { key: prefix, value: value_rlp }.encode(out);
            }
            NodeKind::AccountLeaf {
                ref balance_rlp,
                ref nonce_rlp,
                ref code_hash,
                ref storage_root,
            } => {
                let mut buf = [0u8; 110]; // max RLP length for an account: 2 bytes for list length, 9 for nonce, 33 for
                                          // balance, 33 for storage root, 33 for code hash
                let mut value_rlp = buf.as_mut();
                let storage_root_hash = storage_root
                    .as_ref()
                    .map_or(EMPTY_ROOT_HASH, |p| p.rlp().as_hash().unwrap_or(EMPTY_ROOT_HASH));
                let account_rlp_length = encode_account_leaf(
                    nonce_rlp,
                    balance_rlp,
                    code_hash,
                    &storage_root_hash,
                    &mut value_rlp,
                );
                LeafNodeRef { key: prefix, value: &buf[..account_rlp_length] }.encode(out);
            }
            NodeKind::Branch { ref children } => {
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
        let prefix = self.prefix();
        match self.kind() {
            NodeKind::StorageLeaf { .. } => {
                // this just has to be an estimate for `Vec::with_capacity`
                prefix.len() + 32 + 10 // 10 is just a buffer
            }
            NodeKind::AccountLeaf { .. } => {
                // this just has to be an estimate for `Vec::with_capacity`
                prefix.len() + 32 + 8 + 32 + 37 + 10 // 10 is just a buffer
            }
            NodeKind::Branch { children } => {
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

/// Encodes an account leaf value to RLP format.
///
/// This encodes the account state list: `[nonce, balance, storage_root, code_hash]`
#[inline]
pub fn encode_account_leaf(
    nonce_rlp: &ArrayVec<u8, 9>,
    balance_rlp: &ArrayVec<u8, 33>,
    code_hash: &B256,
    storage_root: &B256,
    out: &mut dyn BufMut,
) -> usize {
    let len = 2 + nonce_rlp.len() + balance_rlp.len() + 33 * 2;
    out.put_u8(0xf8);
    out.put_u8((len - 2) as u8);
    out.put_slice(nonce_rlp);
    out.put_slice(balance_rlp);
    out.put_u8(0xa0);
    out.put_slice(storage_root.as_slice());
    out.put_u8(0xa0);
    out.put_slice(code_hash.as_slice());

    len
}

/// Encodes a branch node to RLP format.
///
/// This encodes the branch node list: `[child0, ..., child15, value]`
/// where each child is either the child's RLP or an empty string (0x80).
#[inline]
pub fn encode_branch(children: &[Option<Pointer>], out: &mut dyn BufMut) -> usize {
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
