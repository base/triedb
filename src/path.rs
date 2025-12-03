use alloy_primitives::{keccak256, Address, StorageKey};
use alloy_trie::Nibbles;
use proptest_derive::Arbitrary;
use std::{fmt, mem, ops::RangeBounds};

pub const ADDRESS_PATH_LENGTH: usize = 64;
pub const STORAGE_PATH_LENGTH: usize = ADDRESS_PATH_LENGTH * 2;

#[inline]
fn is_nibble(x: u8) -> bool {
    x <= 0x0f
}

macro_rules! assert_nibble {
    ( $x:expr ) => {{
        let x = $x;
        ::std::assert!($crate::path::is_nibble(x), "0x{x:02x} is not a nibble")
    }};
}

/// Represents a generic path as a sequence of nibbles.
///
/// `RawPath` objects have a variable size and are guaranteed to be large enough to represent the
/// nibbles from an [`AddressPath`] (64 nibbles) or a [`StoragePath`] (128 nibbles), but attempts
/// to store more nibbles than that may result in panics.
///
/// `RawPath` can be thought of as an extension of [`Nibbles`], which is limited to 64 nibbles.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RawPath {
    nibbles: [u8; 128],
    len: u8,
}

impl RawPath {
    pub const MAX_LEN: usize = 128;

    pub const fn new() -> Self {
        Self { nibbles: [0u8; Self::MAX_LEN], len: 0 }
    }

    pub fn from_nibbles(nibbles: &[u8]) -> Self {
        let mut path = Self::new();
        let len = nibbles.len();
        assert!(len <= Self::MAX_LEN, "too many nibbles to fit into `RawPath`");

        nibbles.iter().copied().for_each(|nibble| assert_nibble!(nibble));
        path.nibbles[..len].copy_from_slice(nibbles);
        path.len = len as u8;

        path
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.len as usize
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn nibbles(&self) -> &[u8] {
        &self.nibbles[..self.len()]
    }

    #[inline]
    fn nibbles_mut(&mut self) -> &mut [u8] {
        let len = self.len();
        &mut self.nibbles[..len]
    }

    #[inline]
    fn nibbles_uninit_mut(&mut self) -> &mut [u8] {
        let len = self.len();
        &mut self.nibbles[len..]
    }

    pub fn get(&self, index: usize) -> Option<u8> {
        if index < self.len() {
            Some(self.nibbles[index])
        } else {
            None
        }
    }

    pub fn get_unchecked(&self, index: usize) -> u8 {
        self.get(index)
            .unwrap_or_else(|| panic!("index out of bounds: {} (len: {})", index, self.len))
    }

    pub fn slice(&self, range: impl RangeBounds<usize>) -> Self {
        let start = range.start_bound().map(|b| *b);
        let end = range.end_bound().map(|b| *b);
        Self::from_nibbles(&self.nibbles()[(start, end)])
    }

    pub fn push(&mut self, nibble: u8) {
        assert_nibble!(nibble);
        *self.nibbles_uninit_mut().first_mut().expect("result does not fit in `RawPath`") = nibble;
        self.len += 1;
    }

    pub fn pop(&mut self) -> u8 {
        let nibble = mem::take(self.nibbles_mut().last_mut().expect("`RawPath` is empty"));
        self.len -= 1;
        nibble
    }

    pub fn extend(&mut self, other: &RawPath) {
        self.nibbles_uninit_mut()
            .get_mut(..other.len())
            .expect("result does not fit in `RawPath`")
            .copy_from_slice(other.nibbles());
        self.len += other.len;
    }

    pub fn join(&self, other: &RawPath) -> Self {
        let mut path = *self;
        path.extend(other);
        path
    }

    pub fn starts_with(&self, other: &RawPath) -> bool {
        if self.len() < other.len() {
            false
        } else {
            self.nibbles[..other.len()] == other.nibbles[..other.len()]
        }
    }

    pub fn common_prefix_length(&self, other: &RawPath) -> usize {
        self.nibbles()
            .iter()
            .copied()
            .zip(other.nibbles().iter().copied())
            .take_while(|(a, b)| a == b)
            .count()
    }

    pub fn truncate(&mut self, new_len: usize) {
        assert!(new_len <= Self::MAX_LEN, "length too large: {new_len}");
        self.nibbles[new_len..].fill(0);
        self.len = new_len as u8;
    }

    pub fn pack<const N: usize>(&self) -> [u8; N] {
        assert_eq!(
            2 * N,
            self.len(),
            "cannot pack {} nibbles into an array of {} bytes",
            self.len(),
            N
        );

        let mut bytes = [0u8; N];
        let mut nibbles = self.nibbles().iter();
        let mut next_nibble = || nibbles.next().expect("unexpected end of nibbles iterator");

        for b in bytes.iter_mut() {
            *b = (next_nibble() << 4) | next_nibble();
        }

        bytes
    }

    pub fn unpack(bytes: &[u8]) -> Self {
        let mut path = Self::new();
        let mut nibbles = path.nibbles.iter_mut();
        let mut next_nibble = || nibbles.next().expect("`bytes` too large to fit in `RawPath`");

        for b in bytes {
            *next_nibble() = b >> 4;
            *next_nibble() = b & 0x0f;
        }

        path.len = (bytes.len() * 2) as u8;
        path
    }

    pub fn lower_64_nibbles(&self) -> Nibbles {
        let nibbles = self.nibbles();
        let nibbles = &nibbles[..nibbles.len().min(64)];
        Nibbles::from_nibbles(nibbles)
    }

    pub fn higher_64_nibbles(&self) -> Nibbles {
        let nibbles = self.nibbles();
        nibbles.get(64..).map(Nibbles::from_nibbles).unwrap_or_default()
    }
}

impl Default for RawPath {
    fn default() -> Self {
        Self::new()
    }
}

impl From<Nibbles> for RawPath {
    fn from(nibbles: Nibbles) -> Self {
        Self::from(&nibbles)
    }
}

impl<'a> From<&'a Nibbles> for RawPath {
    fn from(nibbles: &'a Nibbles) -> Self {
        Self::from_iter(nibbles.iter())
    }
}

impl TryFrom<RawPath> for Nibbles {
    type Error = TryFromRawPathError;

    fn try_from(path: RawPath) -> Result<Self, Self::Error> {
        Self::try_from(&path)
    }
}

impl<'a> TryFrom<&'a RawPath> for Nibbles {
    type Error = TryFromRawPathError;

    fn try_from(path: &'a RawPath) -> Result<Self, Self::Error> {
        if path.len() <= 64 {
            Ok(Nibbles::from_nibbles(path.nibbles()))
        } else {
            Err(TryFromRawPathError(*path))
        }
    }
}

impl FromIterator<u8> for RawPath {
    fn from_iter<I: IntoIterator<Item = u8>>(it: I) -> Self {
        let mut path = Self::new();
        for n in it.into_iter() {
            *path
                .nibbles_uninit_mut()
                .get_mut(0)
                .expect("iterator too large to fit into `RawPath`") = n;
            path.len += 1;
        }
        path
    }
}

impl<'a> FromIterator<&'a u8> for RawPath {
    fn from_iter<I: IntoIterator<Item = &'a u8>>(it: I) -> Self {
        Self::from_iter(it.into_iter().copied())
    }
}

impl fmt::Debug for RawPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct HexNibbles<'a>(&'a [u8]);

        impl<'a> fmt::Debug for HexNibbles<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "0x")?;
                for n in self.0 {
                    write!(f, "{n:x}")?;
                }
                Ok(())
            }
        }

        f.debug_tuple("RawPath").field(&HexNibbles(self.nibbles())).finish()
    }
}

impl proptest::arbitrary::Arbitrary for RawPath {
    type Parameters = proptest::collection::SizeRange;

    type Strategy = proptest::strategy::Map<
        proptest::collection::VecStrategy<core::ops::RangeInclusive<u8>>,
        fn(Vec<u8>) -> Self,
    >;

    fn arbitrary_with(size: Self::Parameters) -> Self::Strategy {
        use proptest::strategy::Strategy;
        proptest::collection::vec(0..=0x0f, size).prop_map(Self::from_iter)
    }
}

pub struct TryFromRawPathError(pub RawPath);

impl fmt::Debug for TryFromRawPathError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "path too long to fit into a Nibbles struct: {:?}", self.0)
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

impl From<AddressPath> for RawPath {
    fn from(a: AddressPath) -> Self {
        Self::from(&a)
    }
}

impl<'a> From<&'a AddressPath> for RawPath {
    fn from(a: &'a AddressPath) -> Self {
        a.path.into()
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

impl From<StoragePath> for RawPath {
    fn from(s: StoragePath) -> Self {
        Self::from(&s)
    }
}

impl<'a> From<&'a StoragePath> for RawPath {
    fn from(s: &'a StoragePath) -> Self {
        RawPath::from(&s.address).join(&RawPath::from(&s.slot))
    }
}

#[cfg(test)]
mod tests {
    mod raw_path {
        use crate::path::RawPath;
        use alloy_trie::Nibbles;

        #[test]
        fn pack() {
            let nibbles = [1, 2, 3, 4];
            let expected_bytes = [0x12, 0x34];

            let p = RawPath::from_nibbles(&nibbles);
            let bytes = p.pack::<2>();
            assert_eq!(bytes, expected_bytes);

            // Verify consistency with `Nibbles`
            let n = Nibbles::from_nibbles(nibbles);
            let bytes = n.pack();
            assert_eq!(&bytes[..2], &expected_bytes);
        }

        #[test]
        fn unpack() {
            let bytes = [0x12, 0x34];
            let expected_nibbles = [1, 2, 3, 4];

            let p = RawPath::unpack(&bytes);
            assert_eq!(p.nibbles(), expected_nibbles);

            // Verify consistency with `Nibbles`
            let n = Nibbles::unpack(bytes);
            assert_eq!(n.to_vec(), expected_nibbles);
        }

        #[test]
        fn to_alloy_trie_nibbles() {
            let nibbles = [1, 2, 3, 4];

            let p = RawPath::from_nibbles(&nibbles);
            let n = Nibbles::try_from(p).expect("conversion from `RawPath` to `Nibbles` failed");

            assert_eq!(n.to_vec(), nibbles);
        }

        #[test]
        fn from_alloy_trie_nibbles() {
            let nibbles = [1, 2, 3, 4];

            let n = Nibbles::from_nibbles(nibbles);
            let p = RawPath::from(n);

            assert_eq!(p.nibbles(), nibbles);
        }

        #[test]
        fn slice() {
            let p = RawPath::from_nibbles(&[1, 2, 3, 4, 5]);
            assert_eq!(p.slice(..), RawPath::from_nibbles(&[1, 2, 3, 4, 5]));
            assert_eq!(p.slice(..3), RawPath::from_nibbles(&[1, 2, 3]));
            assert_eq!(p.slice(..=2), RawPath::from_nibbles(&[1, 2, 3]));
            assert_eq!(p.slice(2..), RawPath::from_nibbles(&[3, 4, 5]));
            assert_eq!(p.slice(1..3), RawPath::from_nibbles(&[2, 3]));
            assert_eq!(p.slice(1..=2), RawPath::from_nibbles(&[2, 3]));
        }

        #[test]
        fn common_prefix_length() {
            let p1 = RawPath::from_nibbles(&[1, 2, 3, 4]);
            let p2 = RawPath::from_nibbles(&[1, 2, 3, 5]);
            assert_eq!(p1.common_prefix_length(&p2), 3);
        }

        #[test]
        fn lower_64_nibbles() {
            let p = RawPath::from_nibbles(&[1, 2, 3, 4]);
            assert_eq!(p.lower_64_nibbles(), Nibbles::from_nibbles([1, 2, 3, 4]));

            let p = RawPath::from_nibbles(&[
                0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3,
                3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6,
                7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10,
                10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12,
                13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15,
                15, 15, 15,
            ]);
            assert_eq!(
                p.lower_64_nibbles(),
                Nibbles::from_nibbles([
                    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3,
                    3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6,
                    6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7,
                ])
            );
        }

        #[test]
        fn higher_64_nibbles() {
            let p = RawPath::from_nibbles(&[
                0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3,
                3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6,
                7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10,
                10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12,
                13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15,
                15, 15, 15,
            ]);
            assert_eq!(
                p.higher_64_nibbles(),
                Nibbles::from_nibbles([
                    8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10,
                    11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13,
                    13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15,
                ])
            );
        }
    }
}
