use std::cmp::min;

use alloy_primitives::{keccak256, Address, StorageKey};
use alloy_trie::Nibbles;
use proptest_derive::Arbitrary;

pub const ADDRESS_PATH_LENGTH: usize = 64;
pub const STORAGE_PATH_LENGTH: usize = ADDRESS_PATH_LENGTH * 2;

/// Path represents a path to a value in the trie.
/// It is composed of two nibble sequences, p1 and p2, for a combined maximum length of 128 nibbles.
/// When p1 is full, it represents a path to an account.
/// When p2 is full, it represents a path to a storage slot.
/// p2 can only be non-empty if p1 is full.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Arbitrary)]
pub struct Path {
    p1: Nibbles,
    p2: Nibbles,
    start_idx: usize,
    end_idx: usize,
}

impl Path {
    pub fn new(p1: Nibbles, p2: Nibbles) -> Self {
        if !p2.is_empty() {
            assert!(
                p1.len() == ADDRESS_PATH_LENGTH,
                "p1 must be 64 nibbles long if p2 is non-empty"
            );
        }
        Self { p1, p2, start_idx: 0, end_idx: p1.len() + p2.len() }
    }

    pub fn len(&self) -> usize {
        self.end_idx - self.start_idx
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn slice(&self, start: usize, end: usize) -> Self {
        assert!(start <= end, "Cannot slice with a start index greater than the end index");
        assert!(
            end <= self.len(),
            "Cannot slice with an end index greater than the length of the path"
        );

        Self {
            p1: self.p1,
            p2: self.p2,
            start_idx: self.start_idx + start,
            end_idx: self.start_idx + end,
        }
    }

    pub fn with_offset(&self, offset: usize) -> Self {
        assert!(
            offset <= self.len(),
            "Cannot offset with an offset greater than the length of the path"
        );

        Self { p1: self.p1, p2: self.p2, start_idx: self.start_idx + offset, end_idx: self.end_idx }
    }

    pub fn get(&self, index: usize) -> Option<u8> {
        let index = self.start_idx + index;
        if index < self.end_idx {
            if index < self.p1.len() {
                self.p1.get(index)
            } else {
                self.p2.get(index - ADDRESS_PATH_LENGTH)
            }
        } else {
            None
        }
    }

    pub fn trunc_to_nibbles(&self) -> Nibbles {
        if self.start_idx == 0 {
            self.p1.slice(..min(self.end_idx, ADDRESS_PATH_LENGTH))
        } else if self.start_idx < ADDRESS_PATH_LENGTH {
            if self.end_idx <= ADDRESS_PATH_LENGTH {
                self.p1.slice(self.start_idx..self.end_idx)
            } else {
                let end_idx = min(self.start_idx, self.end_idx - ADDRESS_PATH_LENGTH);
                self.p1.slice(self.start_idx..).join(&self.p2.slice(..end_idx))
            }
        } else {
            self.p2.slice(self.start_idx - ADDRESS_PATH_LENGTH..self.end_idx - ADDRESS_PATH_LENGTH)
        }
    }
}

/// A path to an `account` in the storage trie.
/// This should contain exactly 64 nibbles, representing the keccak256 hash of an address.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Arbitrary)]
pub struct AddressPath {
    path: Nibbles,
}

impl AddressPath {
    /// Creates a new [AddressPath] from a [Nibbles] slice.
    ///
    /// # Panics
    ///
    /// This function will panic if the provided `Nibbles` slice is not 64 nibbles long.
    pub fn new(path: Nibbles) -> Self {
        assert_eq!(path.len(), ADDRESS_PATH_LENGTH, "Address path must be 64 nibbles long");

        Self { path }
    }

    /// Creates a new [AddressPath] from an [Address].
    pub fn for_address(address: Address) -> Self {
        let hash = keccak256(address);
        Self { path: Nibbles::unpack(hash) }
    }

    /// Returns a reference to the nibbles of the address path.
    pub fn to_nibbles(&self) -> &Nibbles {
        &self.path
    }
}

impl From<AddressPath> for Nibbles {
    fn from(path: AddressPath) -> Self {
        path.path
    }
}

impl<'a> From<&'a AddressPath> for &'a Nibbles {
    fn from(path: &'a AddressPath) -> Self {
        &path.path
    }
}

impl From<AddressPath> for Path {
    fn from(path: AddressPath) -> Self {
        Path::new(path.path, Nibbles::default())
    }
}

/// A path to a `slot` in the storage trie of an `account`.
/// This should contain exactly 64 nibbles, representing the keccak256 hash of an address, followed
/// by 64 nibbles, representing the keccak256 hash of a slot.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Arbitrary)]
pub struct StoragePath {
    address: AddressPath,
    slot: Nibbles,
}

impl StoragePath {
    /// Creates a new [StoragePath] from an [Address] and a [StorageKey].
    pub fn for_address_and_slot(address: Address, slot: StorageKey) -> Self {
        let address_nibbles = AddressPath::for_address(address);
        let slot_hash = keccak256(slot);
        let slot_nibbles = Nibbles::unpack(slot_hash);
        Self { address: address_nibbles, slot: slot_nibbles }
    }

    pub fn for_address_path_and_slot(address_path: AddressPath, slot: StorageKey) -> Self {
        let slot_hash = keccak256(slot);
        let slot_nibbles = Nibbles::unpack(slot_hash);
        Self { address: address_path, slot: slot_nibbles }
    }

    pub fn for_address_path_and_slot_hash(address_path: AddressPath, slot_hash: Nibbles) -> Self {
        Self { address: address_path, slot: slot_hash }
    }

    /// Returns the full 128 nibble path to the storage slot.
    pub fn full_path(&self) -> Path {
        Path::new(*self.address.to_nibbles(), self.slot)
    }

    /// Returns the 64 nibble storage trie portion of the storage path.
    pub fn get_slot(&self) -> &Nibbles {
        &self.slot
    }

    /// Returns the [ADDRESS_PATH_LENGTH] nibble address portion of the storage path.
    pub fn get_address(&self) -> &AddressPath {
        &self.address
    }

    pub fn get_slot_offset(&self) -> usize {
        self.address.path.len()
    }
}

impl From<StoragePath> for Path {
    fn from(path: StoragePath) -> Self {
        path.full_path()
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::hex;

    use super::*;

    #[test]
    fn test_path_slicing() {
        let path = Path::new(
            Nibbles::unpack(hex!(
                "0x1111111111111111111111111111111111111111111111111111111111111111"
            )),
            Nibbles::unpack(hex!(
                "0x2222222222222222222222222222222222222222222222222222222222222222"
            )),
        );
        let sliced_path = path.slice(0, 64);
        assert_eq!(
            sliced_path.trunc_to_nibbles(),
            Nibbles::unpack(hex!(
                "0x1111111111111111111111111111111111111111111111111111111111111111"
            ))
        );
        let sliced_path = path.slice(64, 128);
        assert_eq!(
            sliced_path.trunc_to_nibbles(),
            Nibbles::unpack(hex!(
                "0x2222222222222222222222222222222222222222222222222222222222222222"
            ))
        );
        let sliced_path = path.slice(32, 96);
        assert_eq!(
            sliced_path.trunc_to_nibbles(),
            Nibbles::unpack(hex!(
                "0x1111111111111111111111111111111122222222222222222222222222222222"
            ))
        );
        let sliced_path = path.slice(0, 4);
        assert_eq!(sliced_path.trunc_to_nibbles(), Nibbles::unpack(hex!("0x1111")));
        let sliced_path = path.slice(63, 68);
        assert_eq!(sliced_path.trunc_to_nibbles(), Nibbles::unpack(hex!("0x122220")).slice(..5));
    }

    #[test]
    fn test_path_with_offset() {
        let path = Path::new(
            Nibbles::unpack(hex!(
                "0x1111111111111111111111111111111111111111111111111111111111111111"
            )),
            Nibbles::unpack(hex!(
                "0x2222222222222222222222222222222222222222222222222222222222222222"
            )),
        );
        let offset_path = path.with_offset(62);
        assert_eq!(
            offset_path.trunc_to_nibbles(),
            Nibbles::unpack(hex!(
                "0x1122222222222222222222222222222222222222222222222222222222222222"
            ))
        );
    }

    #[test]
    fn test_get() {
        let path = Path::new(
            Nibbles::unpack(hex!(
                "0x1111111111111111111111111111111111111111111111111111111111111111"
            )),
            Nibbles::unpack(hex!(
                "0x2222222222222222222222222222222222222222222222222222222222222222"
            )),
        );
        assert_eq!(path.get(0), Some(0x1));
        assert_eq!(path.get(63), Some(0x1));
        assert_eq!(path.get(64), Some(0x2));
        assert_eq!(path.get(127), Some(0x2));
        assert_eq!(path.get(128), None);

        let sliced_path = path.slice(62, 80);
        assert_eq!(sliced_path.get(0), Some(0x1));
        assert_eq!(sliced_path.get(1), Some(0x1));
        assert_eq!(sliced_path.get(2), Some(0x2));
        assert_eq!(sliced_path.get(3), Some(0x2));
        assert_eq!(sliced_path.get(17), Some(0x2));
        assert_eq!(sliced_path.get(18), None);
    }
}
