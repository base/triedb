use crate::page::PageId;
use alloy_primitives::B256;
#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct NodeReference {
    pub page_id: PageId,
    pub index: u8,
    // Note: we can assume that the node's RLP representation is always a 32-byte
    // hash because the leaf nodes will contain values >= 32 bytes according to
    // their canonical RLP encoding.
    pub hash: B256,
}

impl NodeReference {
    pub fn new(page_id: PageId, index: u8, hash: B256) -> Self {
        Self { page_id, index, hash }
    }

    pub fn new_dirty(page_id: PageId, index: u8) -> Self {
        Self { page_id, index, hash: B256::ZERO }
    }

    pub fn null() -> Self {
        Self { page_id: u32::MAX, index: 0, hash: B256::ZERO }
    }

    pub fn is_null(&self) -> bool {
        self.page_id == u32::MAX
    }

    pub fn is_dirty(&self) -> bool {
        self.hash == B256::ZERO
    }

    pub fn set_dirty(&mut self) {
        self.hash = B256::ZERO;
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        let mut data = [0u8; 37];
        data[0..4].copy_from_slice(&self.page_id.to_le_bytes());
        data[4] = self.index;
        data[5..].copy_from_slice(self.hash.as_slice());
        data.to_vec()
    }

    pub fn from_bytes(data: &[u8]) -> Self {
        let page_id = PageId::from_le_bytes(data[0..4].try_into().unwrap());
        let index = data[4];
        let hash = B256::from_slice(&data[5..37]);
        Self { page_id, index, hash }
    }
}
