use crate::{meta::MetadataSlot, metrics::TransactionMetrics, page::PageId, snapshot::SnapshotId};
use alloy_primitives::{map::FbBuildHasher, FixedBytes, B256};
use alloy_trie::Nibbles;
use std::collections::HashMap;

/// A map of 64 nibbles (64 bytes). 64 bytes is used instead of 32 bytes to avoid new memory
/// allocations from Nibbles. This is used to store the nibbles of an address in the context.
#[derive(Clone, Debug)]
pub struct B512Map<V>(HashMap<FixedBytes<64>, V, FbBuildHasher<64>>);

impl<V> B512Map<V>
where
    V: Clone,
{
    pub fn with_capacity(capacity: usize) -> Self {
        Self(HashMap::<FixedBytes<64>, V, FbBuildHasher<64>>::with_capacity_and_hasher(
            capacity,
            FbBuildHasher::default(),
        ))
    }

    /// Inserts a key-value pair into the map.
    ///
    /// # Panics
    ///
    /// Panics if the key is not 64 bytes long.
    pub fn insert(&mut self, key: &Nibbles, value: V) {
        self.0.insert(FixedBytes::from_slice(key.as_slice()), value);
    }

    /// Returns the value associated with the key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not 64 bytes long.
    pub fn get(&self, key: &Nibbles) -> Option<V> {
        self.0.get(&FixedBytes::from_slice(key.as_slice())).cloned()
    }

    /// Removes the key-value pair associated with the key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not 64 bytes long.
    pub fn remove(&mut self, key: &Nibbles) {
        self.0.remove(&FixedBytes::from_slice(key.as_slice()));
    }

    /// Removes all elements from the map.
    pub fn clear(&mut self) {
        self.0.clear();
    }
}

#[derive(Clone, Debug)]
pub struct TransactionContext {
    pub(crate) snapshot_id: SnapshotId,
    pub(crate) root_node_hash: B256,
    pub(crate) root_node_page_id: Option<PageId>,
    pub(crate) page_count: u32,
    pub(crate) transaction_metrics: TransactionMetrics,
}

impl TransactionContext {
    pub fn new(meta: impl AsRef<MetadataSlot>) -> Self {
        let meta = meta.as_ref();
        Self {
            snapshot_id: meta.snapshot_id(),
            root_node_hash: meta.root_node_hash(),
            root_node_page_id: meta.root_node_page_id(),
            page_count: meta.page_count(),
            transaction_metrics: Default::default(),
        }
    }

    pub(crate) fn update_metadata(&self, mut meta: impl AsMut<MetadataSlot>) {
        let meta = meta.as_mut();
        meta.set_snapshot_id(self.snapshot_id);
        meta.set_root_node_hash(self.root_node_hash);
        meta.set_root_node_page_id(self.root_node_page_id);
        meta.set_page_count(self.page_count);
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::address;

    use crate::path::AddressPath;

    use super::*;

    #[test]
    fn test_address_nibbles_map() {
        let mut map = B512Map::with_capacity(10);
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let address_path = AddressPath::for_address(address);
        let key = address_path.to_nibbles();
        map.insert(key, (1, 2));
        assert_eq!(map.get(key), Some((1, 2)));
        map.remove(key);
        assert_eq!(map.get(key), None);
    }
}
