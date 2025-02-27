use std::{
    cmp::min,
    fmt::Debug,
    ops::{Deref, Index, Range},
    slice::SliceIndex,
};

use alloy_primitives::{keccak256, Address, StorageKey};
use alloy_trie::Nibbles;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Path {
    nibbles: [u8; 128],
    length: usize,
}

impl Path {
    #[inline]
    pub fn new() -> Self {
        Self {
            nibbles: [0; 128],
            length: 0,
        }
    }

    #[inline]
    pub fn from_nibbles<T: AsRef<[u8]>>(nibbles: T) -> Self {
        Self::from_nibbles_unchecked(nibbles)
    }

    #[inline]
    pub fn new_address_path(path: &[u8]) -> Self {
        assert_eq!(path.len(), 64, "Address path must be 64 nibbles long");
        let mut nibbles = [0u8; 128];
        nibbles[..64].copy_from_slice(path);
        Self {
            nibbles,
            length: 64,
        }
    }

    #[inline]
    pub fn for_address(address: Address) -> Self {
        let hash = keccak256(address);
        Self::unpack(hash)
    }

    #[inline]
    pub fn for_address_and_slot(address: Address, slot: StorageKey) -> Self {
        let address_hash = keccak256(address);
        let slot_hash = keccak256(slot);
        Self::unpack_two(address_hash, slot_hash)
    }

    #[inline]
    pub fn get_slot_path(&self) -> Option<Nibbles> {
        let slot_nibbles = self.nibbles.get(64..)?;
        Some(Nibbles::from_nibbles(slot_nibbles))
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.length
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        &self.nibbles[..self.length]
    }

    #[inline]
    pub fn unpack<T: AsRef<[u8]>>(data: T) -> Self {
        Self::unpack_(data.as_ref())
    }

    #[inline]
    fn unpack_two<T: AsRef<[u8]>>(data1: T, data2: T) -> Self {
        Self::unpack_two_(data1.as_ref(), data2.as_ref())
    }

    #[inline]
    fn unpack_(data: &[u8]) -> Self {
        let unpacked_len = data
            .len()
            .checked_mul(2)
            .expect("trying to unpack usize::MAX / 2 bytes");
        let mut path = [0u8; 128];
        unsafe { Self::unpack_to_unchecked(data, path.as_mut_slice()) };
        Self {
            nibbles: path,
            length: unpacked_len,
        }
    }

    #[inline]
    fn unpack_two_(data1: &[u8], data2: &[u8]) -> Self {
        let unpacked_len = data1
            .len()
            .checked_add(data2.len())
            .expect("trying to unpack usize::MAX / 2 bytes")
            .checked_mul(2)
            .expect("trying to unpack usize::MAX / 2 bytes");
        let mut path = [0u8; 128];
        unsafe {
            Self::unpack_to_unchecked(data1, path.as_mut_slice());
            Self::unpack_to_unchecked(
                data2,
                path.as_mut_slice().get_unchecked_mut(data1.len() * 2..),
            );
        };
        Self {
            nibbles: path,
            length: unpacked_len,
        }
    }

    #[inline]
    pub unsafe fn unpack_to_unchecked(data: &[u8], out: &mut [u8]) {
        debug_assert!(out.len() >= data.len() * 2);
        let ptr = out.as_mut_ptr().cast::<u8>();
        for (i, &byte) in data.iter().enumerate() {
            ptr.add(i * 2).write(byte >> 4);
            ptr.add(i * 2 + 1).write(byte & 0x0f);
        }
    }

    #[inline]
    pub fn from_nibbles_unchecked<T: AsRef<[u8]>>(nibbles: T) -> Self {
        let mut path = [0u8; 128];
        path[..nibbles.as_ref().len()].copy_from_slice(nibbles.as_ref());
        Self {
            nibbles: path,
            length: nibbles.as_ref().len(),
        }
    }

    #[inline]
    pub fn common_prefix_length(&self, other: &[u8]) -> usize {
        common_prefix_length(self, other)
    }

    #[inline]
    pub fn slice<'a, I: Debug>(&'a self, range: I) -> PathRef<'a>
    where
        Self: Index<I, Output = [u8]>,
    {
        PathRef::from_nibbles(&self[range])
    }

    #[inline]
    pub fn get<I>(&self, index: I) -> Option<&<I as SliceIndex<[u8]>>::Output>
    where
        I: SliceIndex<[u8]>,
    {
        self.nibbles[..self.length].get(index)
    }
}

pub struct PathRef<'a> {
    nibbles: &'a [u8],
}

impl<'a> PathRef<'a> {
    pub fn from_nibbles(nibbles: &'a [u8]) -> Self {
        debug_assert!(nibbles.len() <= 128);
        Self { nibbles }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.nibbles.len()
    }

    #[inline]
    pub fn as_path(&self) -> Path {
        Path::from_nibbles_unchecked(self.nibbles)
    }

    #[inline]
    pub fn common_prefix_length(&self, other: &[u8]) -> usize {
        common_prefix_length(self.nibbles, other)
    }

    #[inline]
    pub fn get<I>(&self, index: I) -> Option<&<I as SliceIndex<[u8]>>::Output>
    where
        I: SliceIndex<[u8]>,
    {
        self.nibbles.get(index)
    }
}

impl<'a> AsRef<[u8]> for Path {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl Deref for Path {
    type Target = [u8];
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<'a> Deref for PathRef<'a> {
    type Target = [u8];
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.nibbles
    }
}

impl From<Path> for Nibbles {
    fn from(path: Path) -> Self {
        Nibbles::from_nibbles(path.as_slice())
    }
}

impl<I: SliceIndex<[u8]>> Index<I> for Path {
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output {
        &self.as_slice()[index]
    }
}

#[inline]
pub fn common_prefix_length(a: &[u8], b: &[u8]) -> usize {
    let len = core::cmp::min(a.len(), b.len());
    let a = &a[..len];
    let b = &b[..len];
    for i in 0..len {
        if a[i] != b[i] {
            return i;
        }
    }
    len
}
