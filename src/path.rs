use alloy_primitives::{keccak256, Address, StorageKey};
use alloy_trie::Nibbles;
use proptest_derive::Arbitrary;

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
        assert_eq!(path.len(), 64, "Address path must be 64 nibbles long");

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

/// A path to a `slot` in the storage trie of an `account`.
/// This should contain exactly 64 nibbles, representing the keccak256 hash of an address, followed
/// by 64 nibbles, representing the keccak256 hash of a slot.
#[derive(Debug, Clone, PartialEq, Eq, Arbitrary)]
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

    /// Returns the full 128 nibble path to the storage slot.
    pub fn full_path(&self) -> Nibbles {
        self.address.path.join(&self.slot)
    }

    /// Returns the 64 nibble storage trie portion of the storage path.
    pub fn get_slot(&self) -> &Nibbles {
        &self.slot
    }
}

impl From<StoragePath> for Nibbles {
    fn from(path: StoragePath) -> Self {
        path.full_path()
    }
}
