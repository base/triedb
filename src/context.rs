use crate::{meta::MetadataSlot, metrics::TransactionMetrics, page::PageId, snapshot::SnapshotId};
use alloy_primitives::{map::B256Map, B256};
use alloy_trie::Nibbles;

#[derive(Clone, Debug)]
pub struct TransactionContext {
    pub(crate) snapshot_id: SnapshotId,
    pub(crate) root_node_hash: B256,
    pub(crate) root_node_page_id: Option<PageId>,
    pub(crate) page_count: u32,
    pub(crate) transaction_metrics: TransactionMetrics,
    pub(crate) contract_account_loc_cache: B256Map<(PageId, u8)>,
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
            contract_account_loc_cache: B256Map::with_capacity_and_hasher(10, Default::default()),
        }
    }

    pub(crate) fn update_metadata(&self, mut meta: impl AsMut<MetadataSlot>) {
        let meta = meta.as_mut();
        meta.set_snapshot_id(self.snapshot_id);
        meta.set_root_node_hash(self.root_node_hash);
        meta.set_root_node_page_id(self.root_node_page_id);
        meta.set_page_count(self.page_count);
    }

    pub fn clear_cache(&mut self) {
        self.contract_account_loc_cache.clear();
    }
}

pub fn b256_from_nibbles(mut nibbles: Nibbles) -> B256 {
    B256::from(*nibbles.as_mut_uint_unchecked())
}

#[cfg(test)]
mod tests {
    use alloy_primitives::address;

    use crate::path::AddressPath;

    use super::*;

    #[test]
    fn test_address_nibbles_map() {
        let mut map = B256Map::with_capacity_and_hasher(10, Default::default());
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let address_path = AddressPath::for_address(address);
        let key = b256_from_nibbles(Nibbles::from(address_path));
        map.insert(key, (1, 2));
        assert_eq!(map.get(&key), Some(&(1, 2)));
        map.remove(&key);
        assert_eq!(map.get(&key), None);
    }
}
