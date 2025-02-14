use alloy_trie::Nibbles;

use crate::{
    location::Location,
    page::{PageError, Value},
};

#[derive(Debug)]
pub struct Node<'n> {
    data: &'n [u8],
}

// TODO: this is a dummy node implementation which inefficiently stores a leaf node.
impl<'n> Node<'n> {
    pub fn new(prefix: Nibbles, value: &'n [u8], mut data: &'n mut [u8]) -> Self {
        data[0] = prefix.len() as u8;
        data[1..=prefix.len()].copy_from_slice(prefix.as_slice());
        let value_start = prefix.len() + 1;
        let value_end = value_start + value.len();
        data[value_start..value_end].copy_from_slice(value);
        data = &mut data[..value_end];
        Self { data }
    }

    pub fn prefix(&self) -> Nibbles {
        let prefix_length = self.prefix_length();
        let prefix_data = &self.data[1..=prefix_length as usize];
        Nibbles::from_nibbles(prefix_data)
    }

    pub fn child(&self, index: u8) -> Option<Location> {
        todo!()
    }

    pub fn value(&self) -> Option<&'n [u8]> {
        let prefix_length = self.prefix_length();
        let value_length = self.data.len() - prefix_length as usize - 1;
        Some(&self.data[prefix_length as usize + 1..prefix_length as usize + value_length + 1])
    }

    fn prefix_length(&self) -> u8 {
        self.data[0]
    }
}

impl<'n> TryFrom<&'n [u8]> for Node<'n> {
    type Error = PageError;

    fn try_from(data: &'n [u8]) -> Result<Self, Self::Error> {
        Ok(Self { data })
    }
}

impl<'n> From<Node<'n>> for &'n [u8] {
    fn from(node: Node<'n>) -> Self {
        node.data
    }
}

impl<'n> Value<'n> for Node<'n> {}
