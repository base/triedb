use std::{
    collections::HashMap,
    hash::{BuildHasher, Hasher},
};

use alloy_trie::Nibbles;

struct NibblesHasher {
    state: u64,
}

impl Hasher for NibblesHasher {
    fn finish(&self) -> u64 {
        self.state
    }

    fn write(&mut self, bytes: &[u8]) {
        let mut count = 0;
        for &byte in bytes {
            self.state = (self.state << 8) | (byte as u64);
            count += 1;
            if count >= 8 {
                break;
            }
        }
    }
}

struct NibblesHasherBuilder;

impl BuildHasher for NibblesHasherBuilder {
    type Hasher = NibblesHasher;

    fn build_hasher(&self) -> Self::Hasher {
        NibblesHasher { state: 0 }
    }
}

pub type NibblesMap<V> = HashMap<Nibbles, V, NibblesHasherBuilder>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nibbles_map() {
        let mut map = HashMap::with_hasher(NibblesHasherBuilder);
        let nibbles = Nibbles::from_vec(vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 10, 11, 12, 13, 14, 15]);
        map.insert(nibbles.clone(), "test1");
        assert_eq!(map.get(&nibbles), Some(&"test1"));

        let nibbles2 = Nibbles::from_vec(vec![2, 3, 4, 5, 6, 7, 8, 9, 0, 10, 11, 12, 13, 14, 15]);
        map.insert(nibbles2.clone(), "test2");
        assert_eq!(map.get(&nibbles2), Some(&"test2"));
    }
}
