use crate::page::PageId;
#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct NodeReference {
    pub page_id: PageId,
    pub index: usize,
    pub dirty: bool,
}

impl NodeReference {
    pub fn new(page_id: PageId, index: usize) -> Self {
        Self { page_id, index, dirty: false }
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        let mut data = [0u8; 16];
        data[0..8].copy_from_slice(&self.page_id.to_le_bytes());
        data[8..].copy_from_slice(&(self.index as u64).to_le_bytes());
        data.to_vec()
    }

    pub fn from_bytes(data: &[u8]) -> Self {
        let page_id = PageId::from_le_bytes(data[0..8].try_into().unwrap());
        let index = u64::from_le_bytes(data[8..16].try_into().unwrap());
        Self { page_id, index: index as usize, dirty: false }
    }
}
