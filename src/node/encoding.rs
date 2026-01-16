//! Binary encoding for storing nodes in pages.
//!
//! This module implements the [Value] trait for [Node], which defines how nodes
//! are serialized to and deserialized from the slotted page format.
//!
//! ## Node Type Encoding
//!
//! The first byte encodes the node type:
//! - `0x00`: StorageLeaf
//! - `0x01` (with flags): AccountLeaf
//!   - Bit 7 (0x80): has storage root
//!   - Bit 6 (0x40): has non-empty code hash
//! - `0x02`: Branch

use super::{Node, NodeKind};
use crate::{
    path::RawPath,
    pointer::Pointer,
    storage::value::{self, Value},
};
use alloy_primitives::B256;
use alloy_trie::KECCAK_EMPTY;
use arrayvec::ArrayVec;

impl Value for Node {
    fn size(&self) -> usize {
        let prefix = self.prefix();
        let packed_prefix_length = prefix.len().div_ceil(2);

        match self.kind() {
            NodeKind::StorageLeaf { ref value_rlp } => {
                2 + packed_prefix_length + value_rlp.len() // 2 bytes for type and prefix length
            }
            NodeKind::AccountLeaf {
                ref balance_rlp,
                ref nonce_rlp,
                ref storage_root,
                ref code_hash,
            } => {
                2 + packed_prefix_length +
                    balance_rlp.len() +
                    nonce_rlp.len() +
                    storage_root.is_some() as usize * 37 +
                    (*code_hash != KECCAK_EMPTY) as usize * 32 // 2 bytes for flags and prefix
                                                               // length
            }
            NodeKind::Branch { ref children } => {
                let (_, children_slot_size) = Self::children_slot_size(children);
                2 + packed_prefix_length + 2 + children_slot_size * 37 // 2 bytes for type and
                                                                       // prefix length, 2 for
                                                                       // bitmask, 37 for each child
                                                                       // pointer
            }
        }
    }

    fn serialize_into(&self, buf: &mut [u8]) -> value::Result<usize> {
        let prefix = self.prefix();
        let prefix_length = prefix.len();
        let packed_prefix_length = prefix.len().div_ceil(2);

        if buf.len() < self.size() {
            return Err(value::Error::InvalidEncoding);
        }

        match self.kind() {
            NodeKind::StorageLeaf { value_rlp } => {
                let total_size = 2 + packed_prefix_length + value_rlp.len();

                buf[0] = 0; // StorageLeaf type
                buf[1] = prefix_length as u8;
                prefix.pack_to(buf[2..2 + packed_prefix_length].as_mut());
                buf[2 + packed_prefix_length..].copy_from_slice(value_rlp.as_slice());

                Ok(total_size)
            }
            NodeKind::AccountLeaf { balance_rlp, nonce_rlp, code_hash, storage_root } => {
                let flags = 1 |
                    ((storage_root.is_some() as u8) << 7) |
                    (((*code_hash != KECCAK_EMPTY) as u8) << 6);

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
            NodeKind::Branch { children } => {
                let (total_children, children_slot_size) = Self::children_slot_size(children);

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
        match flags {
            // StorageLeaf
            0 => {
                let prefix_length = bytes[1] as usize;
                let packed_prefix_length = prefix_length.div_ceil(2);
                let mut prefix = RawPath::unpack(&bytes[2..2 + packed_prefix_length]);
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

                Ok(Self::new(prefix.try_into().unwrap(), NodeKind::StorageLeaf { value_rlp }))
            }
            // AccountLeaf
            flags if flags & 1 == 1 => {
                let has_storage = flags & 0b10000000 != 0;
                let has_code = flags & 0b01000000 != 0;
                let prefix_length = bytes[1] as usize;
                let packed_prefix_length = prefix_length.div_ceil(2);
                let mut prefix = RawPath::unpack(&bytes[2..2 + packed_prefix_length]);
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
                    let balance_rlp = ArrayVec::from_iter(
                        bytes[offset..offset + balance_len + 1].iter().copied(),
                    );
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

                Ok(Self::new(
                    prefix.try_into().unwrap(),
                    NodeKind::AccountLeaf { balance_rlp, nonce_rlp, code_hash, storage_root },
                ))
            }
            // Branch
            2 => {
                let prefix_length = bytes[1] as usize;
                let packed_prefix_length = prefix_length.div_ceil(2);
                let mut prefix = RawPath::unpack(&bytes[2..2 + packed_prefix_length]);
                prefix.truncate(prefix_length);

                let children_bitmask = u16::from_be_bytes(
                    bytes[2 + packed_prefix_length..2 + packed_prefix_length + 2]
                        .try_into()
                        .unwrap(),
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

                Ok(Self::new(prefix.try_into().unwrap(), NodeKind::Branch { children }))
            }
            _ => Err(value::Error::InvalidEncoding),
        }
    }
}
