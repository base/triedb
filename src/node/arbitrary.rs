//! Proptest strategies for generating arbitrary nodes.
//!
//! This module contains strategies for fuzzing the node serialization and RLP encoding.

use super::{Node, NodeInner, NodeKind};
use crate::pointer::Pointer;
use alloy_primitives::U256;
use alloy_rlp::encode_fixed_size;
use alloy_trie::Nibbles;
use arrayvec::ArrayVec;
use proptest::{arbitrary, strategy, strategy::Strategy};

pub(super) fn arb_u64_rlp() -> impl Strategy<Value = ArrayVec<u8, 9>> {
    arbitrary::any::<u64>().prop_map(|u| encode_fixed_size(&u)).boxed()
}

pub(super) fn arb_u256_rlp() -> impl Strategy<Value = ArrayVec<u8, 33>> {
    arbitrary::any::<U256>().prop_map(|u| encode_fixed_size(&u)).boxed()
}

pub(super) fn arb_children() -> impl Strategy<Value = [Option<Pointer>; 16]> {
    (proptest::collection::vec(arbitrary::any::<Pointer>(), 2..16), 1..15).prop_map(
        |(children, spacing)| {
            let mut result = [const { None }; 16];
            for (i, child) in children.iter().enumerate() {
                result[(i + spacing as usize) % 16] = Some(child.clone());
            }
            result
        },
    )
}

// Manual implementation of `Arbitrary`, required because `NodeInner` is a private type, and the
// auto implementation would expose it through `Parameters` (making compilation fail).
impl arbitrary::Arbitrary for Node {
    type Parameters = (
        <Nibbles as arbitrary::Arbitrary>::Parameters,
        <NodeKind as arbitrary::Arbitrary>::Parameters,
    );

    type Strategy = strategy::Map<
        (<Nibbles as arbitrary::Arbitrary>::Strategy, <NodeKind as arbitrary::Arbitrary>::Strategy),
        fn((Nibbles, NodeKind)) -> Self,
    >;

    fn arbitrary_with(params: Self::Parameters) -> Self::Strategy {
        let (mut nibbles_params, kind_params) = params;
        nibbles_params = proptest::collection::SizeRange::new(
            nibbles_params.start()..=nibbles_params.end_incl().min(64),
        );
        Strategy::prop_map(
            (
                arbitrary::any_with::<Nibbles>(nibbles_params),
                arbitrary::any_with::<NodeKind>(kind_params),
            ),
            |(prefix, kind)| Self(Box::new(NodeInner { prefix, kind })),
        )
    }
}
