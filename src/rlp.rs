use crate::executor::{Executor, Future, Wait};
use alloy_primitives::B256;
use alloy_rlp::{Decodable, EMPTY_STRING_CODE};
use alloy_trie::nodes::RlpNode;
use proptest::{
    arbitrary::{self, Arbitrary},
    strategy::{self, Strategy},
};
use std::{borrow::Borrow, mem};

const fn empty_hash() -> RlpNode {
    #[repr(C)]
    struct RlpNodeInternal {
        len: u32,
        data: [u8; 33],
    }

    let mut n = RlpNodeInternal { len: 33, data: [0u8; 33] };
    n.data[0] = EMPTY_STRING_CODE + 32;

    // SAFETY: `RlpNode` is a newtype wrapper around `ArrayVec<u8, 33>`, which itself is a
    // `repr(C)` type with the same fields as `RlpNodeInternal`
    unsafe { mem::transmute(n) }
}

static EMPTY_HASH: RlpNode = empty_hash();

/// An [`RlpNode`] whose final value may be computed at a later time, in a separate thread.
///
/// Accessing the `RlpNode` before it has been fully computed will result in a temporary value
/// being returned.
#[derive(Clone, Debug)]
pub struct DeferredRlpNode(Future<RlpNode>);

impl DeferredRlpNode {
    #[inline]
    #[must_use]
    pub fn from_raw(data: &[u8]) -> Option<Self> {
        RlpNode::from_raw(data).map(Self::from)
    }

    #[must_use]
    pub fn from_rlp<E, T>(executor: E, data: T) -> Self
    where
        E: Executor,
        T: Borrow<[u8]>,
    {
        let data = data.borrow();
        if data.len() < 32 {
            // This does not require any hash computation, so no need to run this in a separate
            // thread.
            //
            // SAFETY: `data` is less than the maximum capacity, and `RlpNode::from_raw` is
            // guaranteed not to fail in this case
            unsafe { Self::from_raw(data).unwrap_unchecked() }
        } else {
            // This requires a hash computation.
            let data = data.to_owned();
            Self(executor.defer(move || RlpNode::from_rlp(&data)))
        }
    }

    #[must_use]
    pub fn from_rlp_with<E, F, T>(executor: E, f: F) -> Self
    where
        E: Executor,
        F: FnOnce() -> T + Send + 'static,
        T: Borrow<[u8]>,
    {
        Self(executor.defer(move || {
            let n = RlpNode::from_rlp(f().borrow());
            assert!(
                n.is_hash(),
                "closure passed to DeferredRlpNode::from_rlp_with must generate a hash"
            );
            n
        }))
    }

    #[must_use]
    pub fn word_rlp(word: &B256) -> Self {
        Self::from(RlpNode::word_rlp(word))
    }

    #[inline]
    #[must_use]
    pub fn get(&self) -> Option<&RlpNode> {
        self.0.get()
    }

    #[inline]
    #[must_use]
    pub fn get_or_placeholder(&self) -> &RlpNode {
        // If the `Future` value is not available (`.get()` returns `None`), then it can only mean
        // that this node contains a hash.
        self.get().unwrap_or(&EMPTY_HASH)
    }

    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.get_or_placeholder().len()
    }

    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &[u8] {
        self.get_or_placeholder().as_slice()
    }

    #[inline]
    #[must_use]
    pub fn is_hash(&self) -> bool {
        self.get_or_placeholder().is_hash()
    }

    #[inline]
    #[must_use]
    pub fn as_hash(&self) -> Option<B256> {
        self.get_or_placeholder().as_hash()
    }
}

impl Default for DeferredRlpNode {
    #[inline]
    fn default() -> Self {
        Self(Future::ready(RlpNode::default()))
    }
}

impl From<RlpNode> for DeferredRlpNode {
    #[inline]
    fn from(rlp: RlpNode) -> Self {
        Self(Future::ready(rlp))
    }
}

impl Wait for DeferredRlpNode {
    type Output = RlpNode;

    #[inline]
    fn wait(&self) -> &Self::Output {
        self.0.wait()
    }
}

impl PartialEq for DeferredRlpNode {
    fn eq(&self, other: &Self) -> bool {
        self.wait() == other.wait()
    }
}

impl Eq for DeferredRlpNode {}

impl Decodable for DeferredRlpNode {
    #[inline]
    fn decode(buf: &mut &[u8]) -> alloy_rlp::Result<Self> {
        RlpNode::decode(buf).map(Self::from)
    }
}

impl Arbitrary for DeferredRlpNode {
    type Parameters = <RlpNode as Arbitrary>::Parameters;

    type Strategy = strategy::Map<<RlpNode as Arbitrary>::Strategy, fn(RlpNode) -> Self>;

    fn arbitrary_with(params: Self::Parameters) -> Self::Strategy {
        Strategy::prop_map(arbitrary::any_with::<RlpNode>(params), Self::from)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::Never;

    #[test]
    fn empty_hash() {
        let expected = RlpNode::word_rlp(&B256::ZERO);
        assert_eq!(EMPTY_HASH, expected);
        assert!(EMPTY_HASH.is_hash());
        assert!(EMPTY_HASH.as_hash().unwrap().is_zero());
    }

    #[test]
    fn deferred_is_hash() {
        let node = DeferredRlpNode::from_rlp(Never, [0; 128]);
        assert_eq!(node.get(), None);
        assert!(node.get_or_placeholder().is_hash());
        assert_eq!(node.get_or_placeholder().as_hash(), Some(B256::ZERO));
    }
}
