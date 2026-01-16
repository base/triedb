//! Tests for node serialization and RLP encoding.

use super::*;
use crate::{path::RawPath, pointer::Pointer, storage::value::Value};
use alloy_primitives::{b256, hex, B256, U256};
use alloy_rlp::{encode, Encodable};
use alloy_trie::{nodes::RlpNode, EMPTY_ROOT_HASH, KECCAK_EMPTY};
use proptest::prelude::*;

#[test]
fn test_size_branch() {
    // 2 children, reserve 2 children slots
    let mut node = Node::new_branch(&RawPath::new()).expect("can create node");
    node.set_child(0, Pointer::new(42.into(), RlpNode::from_rlp(&encode(10u8))))
        .expect("should set child");
    node.set_child(11, Pointer::new(11.into(), RlpNode::from_rlp(&encode("foo"))))
        .expect("should set child");
    let size = node.size();
    assert_eq!(size, 2 + 2 + 37 * 2); // 2 bytes for type and prefix length, 2 for bitmask, 37 for each 2 children pointers

    // 3 children, reserve 4 children slots
    let mut node = Node::new_branch(&RawPath::new()).expect("can create node");
    for i in 0..3 {
        node.set_child(i, Pointer::new((i as u32).into(), RlpNode::from_rlp(&encode(i))))
            .expect("should set child");
    }

    let size = node.size();
    assert_eq!(size, 2 + 2 + 37 * 4); // 2 bytes for type and prefix length, 2 for bitmask, 37 for each 4 children pointers

    // 4 children, reserve 4 children slots
    let mut node = Node::new_branch(&RawPath::new()).expect("can create node");
    for i in 10..14 {
        node.set_child(i, Pointer::new((i as u32).into(), RlpNode::from_rlp(&encode(i))))
            .expect("should set child");
    }
    let size = node.size();
    assert_eq!(size, 2 + 2 + 37 * 4); // 2 bytes for type and prefix length, 2 for bitmask, 37 for each 4 children pointers

    // 5 children, reserve 8 children slots
    let mut node = Node::new_branch(&RawPath::new()).expect("can create node");
    for i in 11..16 {
        node.set_child(i, Pointer::new((i as u32).into(), RlpNode::from_rlp(&encode(i))))
            .expect("should set child");
    }
    let size = node.size();
    assert_eq!(size, 2 + 2 + 37 * 8); // 2 bytes for type and prefix length, 2 for bitmask, 37 for each 8 children pointers

    // 8 children, reserve 8 children slots
    let mut node = Node::new_branch(&RawPath::new()).expect("can create node");
    for i in 5..13 {
        node.set_child(i, Pointer::new((i as u32).into(), RlpNode::from_rlp(&encode(i))))
            .expect("should set child");
    }
    let size = node.size();
    assert_eq!(size, 2 + 2 + 37 * 8); // 2 bytes for type and prefix length, 2 for bitmask, 37 for each 8 children pointers

    // 9 children, reserve 16 children slots
    let mut node = Node::new_branch(&RawPath::new()).expect("can create node");
    for i in 3..12 {
        node.set_child(i, Pointer::new((i as u32).into(), RlpNode::from_rlp(&encode(i))))
            .expect("should set child");
    }
    let size = node.size();
    assert_eq!(size, 2 + 2 + 37 * 16); // 2 bytes for type and prefix length, 2 for bitmask, 37
                                       // for each 16 children pointers
}

#[test]
fn test_storage_leaf_node_serialize() {
    let node = Node::new_leaf(
        &RawPath::from_nibbles(&[0xa, 0xb]),
        &TrieValue::Storage(StorageValue::from_be_slice(&[4, 5, 6])),
    )
    .expect("can create node");
    let bytes = node.serialize().unwrap();
    assert_eq!(bytes, hex!("0x0002ab83040506"));

    let node = Node::new_leaf(
        &RawPath::from_nibbles(&[0xa, 0xb, 0xc]),
        &TrieValue::Storage(StorageValue::from_be_slice(&[4, 5, 6, 7])),
    )
    .expect("can create node");
    let bytes = node.serialize().unwrap();
    assert_eq!(bytes, hex!("0x0003abc08404050607"));

    let node = Node::new_leaf(
        &RawPath::new(),
        &TrieValue::Storage(StorageValue::from_be_slice(&[255, 255, 255, 255])),
    )
    .expect("can create node");
    let bytes = node.serialize().unwrap();
    assert_eq!(bytes, hex!("0x000084ffffffff"));

    let node = Node::new_leaf(&RawPath::new(), &TrieValue::Storage(StorageValue::from(0)))
        .expect("can create node");
    let bytes = node.serialize().unwrap();
    assert_eq!(bytes, hex!("0x000080"));

    let node = Node::new_leaf(
        &RawPath::from_nibbles(&hex!(
            "0x000102030405060708090a0b0c0d0e0f000102030405060708090a0b0c0d0e0f"
        )),
        &TrieValue::Storage(StorageValue::from(U256::MAX)),
    )
    .expect("can create node");
    let bytes = node.serialize().unwrap();
    assert_eq!(bytes, hex!("0x00200123456789abcdef0123456789abcdefa0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"));
}

#[test]
fn test_account_leaf_node_serialize() {
    let node = Node::new_leaf(
        &RawPath::from_nibbles(&[0xa, 0xb]),
        &TrieValue::Account(Account::new(
            0,
            U256::from_be_slice(&[4, 5, 6]),
            EMPTY_ROOT_HASH,
            KECCAK_EMPTY,
        )),
    )
    .expect("can create node");
    let bytes = node.serialize().unwrap();
    assert_eq!(bytes, hex!("0x0102ab8083040506"));

    let node = Node::new_leaf(
        &RawPath::from_nibbles(&[0xa, 0xb, 0xc]),
        &TrieValue::Account(Account::new(
            0,
            U256::from_be_slice(&[4, 5, 6, 7]),
            EMPTY_ROOT_HASH,
            KECCAK_EMPTY,
        )),
    )
    .expect("can create node");
    let bytes = node.serialize().unwrap();
    assert_eq!(bytes, hex!("0x0103abc0808404050607"));

    let node = Node::new_leaf(
        &RawPath::new(),
        &TrieValue::Account(Account::new(
            0,
            U256::from_be_slice(&[0xf, 0xf, 0xf, 0xf]),
            EMPTY_ROOT_HASH,
            b256!("0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"),
        )),
    )
    .expect("can create node");
    let bytes = node.serialize().unwrap();
    assert_eq!(
        bytes,
        hex!("0x410080840f0f0f0fdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef")
    );

    let mut node = Node::new_leaf(
        &RawPath::new(),
        &TrieValue::Account(Account::new(
            0,
            U256::from_be_slice(&[0xf, 0xf, 0xf, 0xf]),
            EMPTY_ROOT_HASH,
            b256!("0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"),
        )),
    )
    .expect("can create node");
    node.set_child(
        0,
        Pointer::new(
            42.into(),
            RlpNode::word_rlp(&b256!(
                "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
            )),
        ),
    )
    .expect("should set child");
    let bytes = node.serialize().unwrap();
    assert_eq!(bytes, hex!("0xc10080840f0f0f0fdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef0000002a011234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"));
}

#[test]
fn test_branch_node_serialize() {
    let mut node: Node = Node::new_branch(&RawPath::new()).expect("can create node");
    let hash1 = b256!("0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef");
    let hash2 = b256!("0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
    node.set_child(0, Pointer::new(42.into(), RlpNode::word_rlp(&hash1)))
        .expect("should set child");
    node.set_child(11, Pointer::new(43.into(), RlpNode::word_rlp(&hash2)))
        .expect("should set child");
    let bytes = node.serialize().unwrap();
    assert_eq!(bytes.len(), 2 + 2 + 37 * 2);
    // branch, no prefix
    let mut expected = Vec::from([2, 0]);
    // children bitmask (10000000 00010000)
    expected.extend([128, 16]);
    // child 0
    expected.extend([0, 0, 0, 42, 1]);
    expected.extend(hash1.as_slice());
    // child 11
    expected.extend([0, 0, 0, 43, 1]);
    expected.extend(hash2.as_slice());
    // children 12-15
    assert_eq!(bytes, expected);

    let mut node: Node = Node::new_branch(&RawPath::from_nibbles(&[0xa, 0xb, 0xc, 0xd, 0xe]))
        .expect("can create node");
    let hash1 = b256!("0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef");
    let hash2 = b256!("0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
    let hash3 = b256!("0x1111111111111111111111111111111111111111111111111111111111111111");
    node.set_child(2, Pointer::new(100.into(), RlpNode::word_rlp(&hash1)))
        .expect("should set child");
    node.set_child(3, Pointer::new(200.into(), RlpNode::word_rlp(&hash2)))
        .expect("should set child");
    node.set_child(15, Pointer::new(210.into(), RlpNode::word_rlp(&hash3)))
        .expect("should set child");
    let bytes = node.serialize().unwrap();
    assert_eq!(bytes.len(), 2 + 3 + 2 + 37 * 4);
    // branch, length, prefix
    let mut expected = Vec::from([2, 5, 171, 205, 224]);
    // children bitmask (00110000 00000001)
    expected.extend([48, 1]);
    // child 2
    expected.extend([0, 0, 0, 100, 1]);
    expected.extend(hash1.as_slice());
    // child 3
    expected.extend([0, 0, 0, 200, 1]);
    expected.extend(hash2.as_slice());
    // child 15
    expected.extend([0, 0, 0, 210, 1]);
    expected.extend(hash3.as_slice());
    // remaining empty slot
    expected.extend([0; 37]);
    assert_eq!(bytes, expected);

    let mut node: Node =
        Node::new_branch(&RawPath::from_nibbles(&[0x0, 0x0])).expect("can create node");
    let v1 = encode(1u8);
    let v2 = encode("hello world");
    node.set_child(1, Pointer::new(99999.into(), RlpNode::from_rlp(&v1)))
        .expect("should set child");
    node.set_child(2, Pointer::new(8675309.into(), RlpNode::from_rlp(&v2)))
        .expect("should set child");
    let bytes = node.serialize().unwrap();

    // branch, length, prefix
    let mut expected = Vec::from([2, 2, 0]);
    // children bitmask (01100000 00000000)
    expected.extend([96, 0]);
    // child 1
    expected.extend([0, 1, 134, 159, 0]);
    expected.extend(v1);
    expected.extend([0; 31]);
    // child 2
    expected.extend([0, 132, 95, 237, 0]);
    expected.extend(v2);
    expected.extend([0; 20]);
    assert_eq!(bytes, expected);
}

#[test]
fn test_leaf_node_encode() {
    let node = Node::new_leaf(
        &RawPath::new(),
        &TrieValue::Account(Account::new(0, U256::from(1), B256::ZERO, B256::ZERO)),
    )
    .expect("can create node");
    let mut bytes = vec![];
    node.encode(&mut bytes);
    assert_eq!(bytes, hex!("0xf84920b846f8448001a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a00000000000000000000000000000000000000000000000000000000000000000"));

    let node = Node::new_leaf(
        &RawPath::from_nibbles(&[0xa, 0xb]),
        &TrieValue::Account(Account::new(1, U256::from(100), B256::ZERO, B256::ZERO)),
    )
    .expect("can create node");
    let mut bytes = vec![];
    node.encode(&mut bytes);
    assert_eq!(bytes, hex!("0xf84b8220abb846f8440164a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a00000000000000000000000000000000000000000000000000000000000000000"));

    let node = Node::new_leaf(
        &RawPath::from_nibbles(&[0xa, 0xb, 0xc, 0xd, 0xe]),
        &TrieValue::Account(Account::new(999, U256::from(123456789), B256::ZERO, B256::ZERO)),
    )
    .expect("can create node");
    let mut bytes = vec![];
    node.encode(&mut bytes);
    assert_eq!(bytes, hex!("0xf852833abcdeb84cf84a8203e784075bcd15a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a00000000000000000000000000000000000000000000000000000000000000000"));

    let node = Node::new_leaf(
        &RawPath::unpack(&hex!(
            "0x761d5c42184a02cc64585ed2ff339fc39a907e82731d70313c83d2212b2da36b"
        )),
        &TrieValue::Account(Account::new(
            0,
            U256::from(10_000_000_000_000_000_000u64),
            EMPTY_ROOT_HASH,
            KECCAK_EMPTY,
        )),
    )
    .expect("can create node");
    let mut bytes = vec![];
    node.encode(&mut bytes);
    assert_eq!(bytes, hex!("0xf872a120761d5c42184a02cc64585ed2ff339fc39a907e82731d70313c83d2212b2da36bb84ef84c80888ac7230489e80000a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"));
    let rlp_encoded = node.to_rlp_node();
    // hash prefixed with 0xa0 (length 32)
    assert_eq!(
        rlp_encoded.as_slice(),
        hex!("0xa0337e249c268401079fc728c58142710845805285dbc90e7c71bb1b79b9d7a745")
    );
}

#[test]
fn test_branch_node_encode() {
    let mut node = Node::new_branch(&RawPath::new()).expect("can create node");
    node.set_child(
        0,
        Pointer::new(
            0.into(),
            RlpNode::word_rlp(&b256!(
                "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
            )),
        ),
    )
    .expect("should set child");
    node.set_child(
        15,
        Pointer::new(
            15.into(),
            RlpNode::word_rlp(&b256!(
                "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
            )),
        ),
    )
    .expect("should set child");
    let mut bytes = vec![];
    node.encode(&mut bytes);
    assert_eq!(bytes, hex!("0xf851a01234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef8080808080808080808080808080a0deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef80"));

    let mut node = Node::new_branch(&RawPath::new()).expect("can create node");
    node.set_child(
        3,
        Pointer::new(
            0.into(),
            RlpNode::word_rlp(&b256!(
                "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
            )),
        ),
    )
    .expect("should set child");
    node.set_child(
        7,
        Pointer::new(
            15.into(),
            RlpNode::word_rlp(&b256!(
                "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
            )),
        ),
    )
    .expect("should set child");
    node.set_child(
        13,
        Pointer::new(
            13.into(),
            RlpNode::word_rlp(&b256!(
                "0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f"
            )),
        ),
    )
    .expect("should set child");
    let mut bytes = vec![];
    node.encode(&mut bytes);
    assert_eq!(bytes, hex!("0xf871808080a01234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef808080a0deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef8080808080a0f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f808080"));

    let mut node = Node::new_branch(&RawPath::from_nibbles(&[0x1, 0x2])).expect("can create node");
    node.set_child(
        0,
        Pointer::new(
            0.into(),
            RlpNode::word_rlp(&b256!(
                "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
            )),
        ),
    )
    .expect("should set child");
    node.set_child(
        15,
        Pointer::new(
            15.into(),
            RlpNode::word_rlp(&b256!(
                "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
            )),
        ),
    )
    .expect("should set child");
    let mut bytes = vec![];
    node.encode(&mut bytes);
    assert_eq!(
        bytes,
        hex!("0xe4820012a07bd949f8cd65627b2b00e38e837d3d6136a9fd1599e3677a4b5a730e2176f67d")
    );

    let mut node = Node::new_branch(&RawPath::from_nibbles(&[0x7, 0x7, 0x7, 0x7, 0x7, 0x7, 0x7]))
        .expect("can create node");
    node.set_child(
        3,
        Pointer::new(
            0.into(),
            RlpNode::word_rlp(&b256!(
                "0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
            )),
        ),
    )
    .expect("should set child");
    node.set_child(
        7,
        Pointer::new(
            15.into(),
            RlpNode::word_rlp(&b256!(
                "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
            )),
        ),
    )
    .expect("should set child");
    node.set_child(
        13,
        Pointer::new(
            13.into(),
            RlpNode::word_rlp(&b256!(
                "0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f"
            )),
        ),
    )
    .expect("should set child");
    let encoded = encode(&node);
    node.encode(&mut bytes);
    assert_eq!(
        encoded,
        hex!("0xe68417777777a0dea7c3591d20f8be14c2ae9448648a7c4f7e63f3bad1ae7bf750871a66d3b95b")
    );

    let mut node = Node::new_branch(&RawPath::new()).expect("can create node");
    node.set_child(
        5,
        Pointer::new(
            5.into(),
            RlpNode::word_rlp(&b256!(
                "0x18e3b46e84b35270116303fb2a33c853861d45d99da2d87117c2136f7edbd0b9"
            )),
        ),
    )
    .expect("should set child");
    node.set_child(
        7,
        Pointer::new(
            7.into(),
            RlpNode::word_rlp(&b256!(
                "0x717aef38e7ba4a0ae477856a6e7f6ba8d4ee764c57908e6f22643a558db737ff"
            )),
        ),
    )
    .expect("should set child");
    let encoded = encode(&node);
    assert_eq!(
        encoded,
        hex!(
            "0xf8518080808080a018e3b46e84b35270116303fb2a33c853861d45d99da2d87117c2136f7edbd0b980a0717aef38e7ba4a0ae477856a6e7f6ba8d4ee764c57908e6f22643a558db737ff808080808080808080"
        )
    );
    let rlp_encoded = node.to_rlp_node();
    // hash prefixed with 0xa0 (length 32)
    assert_eq!(
        rlp_encoded.as_slice(),
        hex!("0xa00d9348243d7357c491e6a61f4b1305e77dc6acacdb8cc708e662f6a9bab6ca02")
    );
}

proptest! {
    #[test]
    fn fuzz_node_to_from_bytes(node: Node) {
        let bytes = node.serialize().unwrap();
        let decoded = Node::from_bytes(&bytes).unwrap();
        assert_eq!(node, decoded);
    }

    #[test]
    fn fuzz_node_rlp_encode(node: Node) {
        node.to_rlp_node();
    }
}
