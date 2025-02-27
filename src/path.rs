use alloy_primitives::{keccak256, Address, StorageKey};
use alloy_trie::Nibbles;
use proptest_derive::Arbitrary;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Arbitrary)]
pub struct AddressPath {
    path: Nibbles,
}

impl AddressPath {
    pub fn new(path: Nibbles) -> Self {
        assert_eq!(path.len(), 64, "Address path must be 64 nibbles long");

        Self { path }
    }

    pub fn for_address(address: Address) -> Self {
        let hash = keccak256(address);
        Self {
            path: Nibbles::unpack(hash),
        }
    }
}

impl From<AddressPath> for Nibbles {
    fn from(path: AddressPath) -> Self {
        path.path
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Arbitrary)]
pub struct StoragePath {
    address: AddressPath,
    slot: Nibbles,
}

impl StoragePath {
    pub fn for_address_and_slot(address: Address, slot: StorageKey) -> Self {
        let address_nibbles = AddressPath::for_address(address);
        let slot_hash = keccak256(slot);
        let slot_nibbles = Nibbles::unpack(slot_hash);
        Self {
            address: address_nibbles,
            slot: slot_nibbles,
        }
    }

    pub fn full_path(&self) -> Nibbles {
        self.address.path.join(&self.slot)
    }

    pub fn get_slot(&self) -> Nibbles {
        self.slot.clone()
    }
}
