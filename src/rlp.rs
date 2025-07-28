use alloy_trie::nodes::RlpNode;
use lazy_static::lazy_static;
use alloy_primitives::B256;
use alloy_rlp::Decodable;
use crate::executor::Future;
use crate::executor::Executor;
use crate::executor::Wait;
use std::borrow::Borrow;
use proptest::arbitrary::{self, Arbitrary};
use proptest::strategy::{self, Strategy};

// TODO: This uses a `lazy_static` because `RlpNode` constructors are non-const, but we can use
// some tricks to come up with our own const contructor.
lazy_static! {
    static ref EMPTY_HASH: RlpNode = RlpNode::word_rlp(&B256::ZERO);
}

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
        where E: Executor, T: Borrow<[u8]>,
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
        where E: Executor, F: FnOnce() -> T + Send + 'static, T: Borrow<[u8]> {
        Self(executor.defer(move || RlpNode::from_rlp(f().borrow())))
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
        //
        // TODO: the above assumption is not true because of `from_rlp_with`
        self.get().unwrap_or(&*EMPTY_HASH)
    }

    //#[inline]
    //#[must_use]
    //pub fn as_rlp_node(&self) -> Option<&RlpNode> {
    //    self.0.get()
    //}

    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.get_or_placeholder().len()
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

//impl PartialEq<Self> for DeferredRlpNode {
//    #[inline]
//    fn eq(&self, other: &Self) -> bool {
//        self.as_rlp_node() == other.as_rlp_node()
//    }
//}
//
//impl PartialEq<RlpNode> for DeferredRlpNode {
//    #[inline]
//    fn eq(&self, other: &RlpNode) -> bool {
//        self.as_rlp_node() == other
//    }
//}
//
//impl PartialEq<DeferredRlpNode> for RlpNode {
//    #[inline]
//    fn eq(&self, other: &DeferredRlpNode) -> bool {
//        self == other.as_rlp_node()
//    }
//}
//
//impl Eq for DeferredRlpNode {}

//impl Deref for DeferredRlpNode {
//    type Target = RlpNode;
//
//    #[inline]
//    fn deref(&self) -> &Self::Target {
//        self.as_rlp_node()
//    }
//}
//
//impl Borrow<RlpNode> for DeferredRlpNode {
//    #[inline]
//    fn borrow(&self) -> &RlpNode {
//        self.as_rlp_node()
//    }
//}
//
//impl AsRef<RlpNode> for DeferredRlpNode {
//    #[inline]
//    fn as_ref(&self) -> &RlpNode {
//        self.as_rlp_node()
//    }
//}
//
//impl Borrow<[u8]> for DeferredRlpNode {
//    #[inline]
//    fn borrow(&self) -> &[u8] {
//        self.as_rlp_node().as_slice()
//    }
//}
//
//impl AsRef<[u8]> for DeferredRlpNode {
//    #[inline]
//    fn as_ref(&self) -> &[u8] {
//        self.as_rlp_node().as_slice()
//    }
//}

impl Wait for DeferredRlpNode {
    type Output = RlpNode;

    #[inline]
    fn wait(&self) -> &Self::Output {
        self.0.wait()
    }
}

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
        Strategy::prop_map(
                arbitrary::any_with::<RlpNode>(params), Self::from)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::Never;

    #[test]
    fn deferred_is_hash() {
        let node = DeferredRlpNode::from_rlp(Never, [0; 128]);
        assert_eq!(node.get(), None);
        assert!(node.get_or_placeholder().is_hash());
        assert_eq!(node.get_or_placeholder().as_hash(), Some(B256::ZERO));
    }
}
