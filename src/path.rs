use std::{
    cmp::min,
    ops::{Bound, RangeBounds},
};

use alloy_primitives::{keccak256, Address, StorageKey};
use alloy_trie::Nibbles;
use proptest::arbitrary;
use proptest_derive::Arbitrary;

pub const ADDRESS_PATH_LENGTH: usize = 64;
pub const STORAGE_PATH_LENGTH: usize = ADDRESS_PATH_LENGTH * 2;

/// Path represents a path to a value in the trie.
/// It is composed of two nibble sequences, p1 and p2, for a combined maximum length of 128 nibbles.
/// When p1 is full, it represents a path to an account.
/// When p2 is full, it represents a path to a storage slot.
/// p2 can only be non-empty if p1 is full.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TriePath {
    p1: Nibbles,
    p2: Nibbles,
}

impl TriePath {
    const NIBBLE_LENGTH: usize = 64;
    const NIBBLE_BYTES: usize = 32;

    pub fn new(p1: Nibbles, p2: Nibbles) -> Self {
        if !p2.is_empty() {
            assert!(
                p1.len() == Self::NIBBLE_LENGTH,
                "p1 must be 64 nibbles long if p2 is non-empty"
            );
        }
        Self { p1, p2 }
    }

    pub fn new_short(p1: Nibbles) -> Self {
        Self::new(p1, Nibbles::default())
    }

    pub fn from_nibbles<T: AsRef<[u8]>>(nibbles: T) -> Self {
        if nibbles.as_ref().len() <= Self::NIBBLE_LENGTH {
            let p1 = Nibbles::from_nibbles(nibbles.as_ref());
            Self::new_short(p1)
        } else {
            let p1 = Nibbles::from_nibbles(&nibbles.as_ref()[..Self::NIBBLE_LENGTH]);
            let p2 = Nibbles::from_nibbles(&nibbles.as_ref()[Self::NIBBLE_LENGTH..]);
            Self::new(p1, p2)
        }
    }

    pub fn unpack(data: impl AsRef<[u8]>) -> Self {
        if data.as_ref().len() <= Self::NIBBLE_BYTES {
            let p1 = Nibbles::unpack(data.as_ref());
            Self::new_short(p1)
        } else {
            let p1 = Nibbles::unpack(&data.as_ref()[..Self::NIBBLE_BYTES]);
            let p2 = Nibbles::unpack(&data.as_ref()[Self::NIBBLE_BYTES..]);
            Self::new(p1, p2)
        }
    }

    pub const fn len(&self) -> usize {
        self.p1.len() + self.p2.len()
    }

    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn slice(&self, range: impl RangeBounds<usize>) -> Self {
        // Determine the start and end nibble indices from the range bounds
        let start = match range.start_bound() {
            Bound::Included(&idx) => idx,
            Bound::Excluded(&idx) => idx + 1,
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(&idx) => idx + 1,
            Bound::Excluded(&idx) => idx,
            Bound::Unbounded => self.len(),
        };
        assert!(start <= end, "Cannot slice with a start index greater than the end index");
        assert!(
            end <= self.len(),
            "Cannot slice with an end index greater than the length of the path"
        );

        if start == 0 {
            let p2_end_idx = if end <= Self::NIBBLE_LENGTH { 0 } else { self.p2_idx(end) };
            Self::new(self.p1.slice(..min(end, self.p1.len())), self.p2.slice(..p2_end_idx))
        } else if start < Self::NIBBLE_LENGTH {
            if end <= Self::NIBBLE_LENGTH {
                Self::new_short(self.p1.slice(start..end))
            } else {
                let p2_end_idx = self.p2_idx(end);
                let p2_split_idx = min(start, p2_end_idx);
                Self::new(
                    self.p1.slice(start..).join(&self.p2.slice(..p2_split_idx)),
                    self.p2.slice(p2_split_idx..p2_end_idx),
                )
            }
        } else {
            Self::new_short(self.p2.slice(self.p2_idx(start)..self.p2_idx(end)))
        }
    }

    pub fn with_offset(&self, offset: usize) -> Self {
        self.slice(offset..)
    }

    pub fn get(&self, index: usize) -> Option<u8> {
        if index < Self::NIBBLE_LENGTH {
            self.p1.get(index)
        } else {
            self.p2.get(self.p2_idx(index))
        }
    }

    pub fn trunc_to_nibbles(&self) -> Nibbles {
        self.p1
    }

    const fn p2_idx(&self, index: usize) -> usize {
        index - Self::NIBBLE_LENGTH
    }
}

impl TryFrom<TriePath> for Nibbles {
    type Error = ();

    fn try_from(value: TriePath) -> Result<Self, Self::Error> {
        if value.p2.is_empty() {
            Ok(value.p1)
        } else {
            Err(())
        }
    }
}

impl<'a> TryFrom<&'a TriePath> for &'a Nibbles {
    type Error = ();

    fn try_from(value: &'a TriePath) -> Result<Self, Self::Error> {
        if value.p2.is_empty() {
            Ok(&value.p1)
        } else {
            Err(())
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

impl From<AddressPath> for TriePath {
    fn from(path: AddressPath) -> Self {
        TriePath::new_short(path.path)
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
    pub fn full_path(&self) -> TriePath {
        TriePath::new(*self.address.to_nibbles(), self.slot)
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

impl From<StoragePath> for TriePath {
    fn from(path: StoragePath) -> Self {
        TriePath::new(path.address.path, path.slot)
    }
}

// Manual implementation of `Arbitrary`, required becuase `TriePath` forbids the use of non-empty p2
// with non-full p1.
impl arbitrary::Arbitrary for TriePath {
    type Parameters = proptest::collection::SizeRange;
    type Strategy = proptest::strategy::Map<
        proptest::collection::VecStrategy<core::ops::RangeInclusive<u8>>,
        fn(Vec<u8>) -> Self,
    >;

    #[inline]
    fn arbitrary() -> Self::Strategy {
        Self::arbitrary_with(Self::Parameters::new(0..=128))
    }

    #[inline]
    fn arbitrary_with(size: proptest::collection::SizeRange) -> Self::Strategy {
        use proptest::prelude::*;
        proptest::collection::vec(0x0..=0xf, size).prop_map(Self::from_nibbles)
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::hex;
    use proptest::prelude::*;

    use super::*;

    #[test]
    fn test_path_slicing() {
        let path = TriePath::new(
            Nibbles::unpack(hex!(
                "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
            )),
            Nibbles::unpack(hex!(
                "0xf33df00df33df00df33df00df33df00df33df00df33df00df33df00df33df00d"
            )),
        );
        let sliced_path = path.slice(..);
        assert_eq!(sliced_path, path);

        let sliced_path = path.slice(0..128);
        assert_eq!(sliced_path, path);

        let sliced_path = path.slice(..64);
        assert_eq!(
            sliced_path,
            TriePath::unpack(hex!(
                "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
            ))
        );
        let sliced_path = path.slice(64..);
        assert_eq!(
            sliced_path,
            TriePath::unpack(hex!(
                "0xf33df00df33df00df33df00df33df00df33df00df33df00df33df00df33df00d"
            ))
        );
        let sliced_path = path.slice(32..90);
        assert_eq!(
            sliced_path,
            TriePath::unpack(hex!("0xdeadbeefdeadbeefdeadbeefdeadbeeff33df00df33df00df33df00df3"))
        );
        let sliced_path = path.slice(..4);
        assert_eq!(sliced_path, TriePath::unpack(hex!("0xdead")));
        let sliced_path = path.slice(63..68);
        assert_eq!(sliced_path, TriePath::from_nibbles([0xf, 0xf, 0x3, 0x3, 0xd]));
    }

    #[test]
    fn test_path_with_offset() {
        let path = TriePath::new(
            Nibbles::unpack(hex!(
                "0x1111111111111111111111111111111111111111111111111111111111111111"
            )),
            Nibbles::unpack(hex!(
                "0x2222222222222222222222222222222222222222222222222222222222222222"
            )),
        );
        let offset_path = path.with_offset(62);
        assert_eq!(
            offset_path,
            TriePath::unpack(hex!(
                "0x112222222222222222222222222222222222222222222222222222222222222222"
            ))
        );
    }

    #[test]
    fn test_get() {
        let path = TriePath::new(
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

        let sliced_path = path.slice(62..80);
        assert_eq!(sliced_path.get(0), Some(0x1));
        assert_eq!(sliced_path.get(1), Some(0x1));
        assert_eq!(sliced_path.get(2), Some(0x2));
        assert_eq!(sliced_path.get(3), Some(0x2));
        assert_eq!(sliced_path.get(17), Some(0x2));
        assert_eq!(sliced_path.get(18), None);
    }

    fn valid_slice_inputs() -> impl Strategy<Value = (TriePath, usize, usize)> {
        any::<TriePath>().prop_flat_map(|path| {
            let len = path.len();
            (Just(path), 0..=len)
                .prop_flat_map(move |(path, start)| (Just(path), Just(start), start..=len))
        })
    }

    proptest! {
        #[test]
        fn fuzz_get(path: TriePath) {
            for i in 0..path.len() {
                path.get(i);
            }
        }

        #[test]
        fn fuzz_slice((path, start, end) in valid_slice_inputs()) {
            let sliced_path = path.slice(start..end);
            assert_eq!(sliced_path.len(), end - start);
        }
    }
}
