use alloy_trie::Nibbles;

use crate::page::PageId;

pub trait Branch {
    fn prefix_length(&self) -> u8;
    fn prefix(&self) -> Nibbles;
    fn child(&self, index: u8) -> Option<PageId>;
}

pub struct BranchSlice<'b> {
    data: &'b [u8],
}

impl<'b> BranchSlice<'b> {
    pub fn new() -> Self {}
}

impl<'b> Branch for BranchSlice<'b> {
    fn prefix_length(&self) -> u8 {
        self.data[0]
    }

    fn prefix(&self) -> Nibbles {
        Nibbles::new(&self.data[1..self.prefix_length() as usize])
    }

    fn child(&self, index: u8) -> Option<PageId> {
        todo!()
    }
}

impl<'b> TryFrom<&'b [u8]> for BranchSlice<'b> {
    type Error = ();

    fn try_from(data: &'b [u8]) -> Result<Self, Self::Error> {
        Ok(Self { data })
    }
}
