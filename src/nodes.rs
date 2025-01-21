pub mod branch;
pub mod leaf;
pub mod reference;

use alloy_trie::Nibbles;
use branch::BranchNode;
use leaf::LeafNode;
use crate::value::Value;
use crate::page_manager::PageManager;
pub struct Trie<V: Value, R: PageManager> {
    root: TrieNode<V>,
    path_length: usize,
    resolver: R,
}

impl<V: Value, R: PageManager> Trie<V, R> {
    pub fn new(path_length: usize, resolver: R) -> Self {
        Self { root: TrieNode::new_empty_root(), path_length, resolver }
    }

    // pub fn insert(&mut self, path: Nibbles, value: V) {
    //     assert!(path.len() == self.path_length, "Path length must match the trie's path length");
    //     self.root = mem::take(&mut self.root).insert(path, value);
    // }

    // pub fn get(&self, path: Nibbles) -> Option<&V> {
    //     if path.len() != self.path_length {
    //         return None;
    //     }

    //     self.root.get(path)
    // }

    // pub fn remove(&mut self, path: Nibbles) -> bool {
    //     if path.len() != self.path_length {
    //         return false;
    //     }

    //     let (new_root, removed) = mem::take(&mut self.root).remove(path);
    //     self.root = new_root;
    //     removed
    // }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum TrieNode<V: Value> {
    #[default]
    EmptyRoot,
    Leaf(LeafNode<V>),
    Branch(BranchNode),
}

impl<V: Value> TrieNode<V> {
    pub fn new_empty_root() -> Self {
        Self::EmptyRoot
    }

    pub fn encoded_size(&self) -> usize {
        // TODO: make this more efficient
        self.as_bytes().len()
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        match self {
            Self::EmptyRoot => vec![0u8; 0],
            Self::Leaf(leaf) => {
                let mut bytes = vec![1u8];
                bytes.append(&mut leaf.as_bytes());
                bytes
            }
            Self::Branch(branch) => {
                let mut bytes = vec![2u8];
                bytes.append(&mut branch.as_bytes());
                bytes
            }
        }
    }

    pub fn from_bytes(bytes: &[u8]) -> Self {
        match bytes[0] {
            0 => Self::EmptyRoot,
            1 => Self::Leaf(LeafNode::from_bytes(&bytes[1..])),
            2 => Self::Branch(BranchNode::from_bytes(&bytes[1..])),
            _ => panic!("Invalid node type"),
        }
    }

    // pub fn insert(self, path: Nibbles, value: V) -> Self {
    //     match self {
    //         Self::EmptyRoot => {
    //             Self::Leaf(LeafNode::new(path, value))
    //         }
    //         Self::Leaf(leaf) => {
    //             let common_prefix_len = path.common_prefix_length(&leaf.prefix);

    //             if common_prefix_len == leaf.prefix.len() {
    //                 if common_prefix_len == path.len() {
    //                     // full path match, replace the leaf value
    //                     leaf.with_value(value).into()
    //                 } else {
    //                     // new path is a superset of the leaf path, this is forbidden
    //                     panic!("New value has a longer path than an existing leaf node");
    //                 }
    //             } else {
    //                 // create a new branch at the common prefix
    //                 let common_prefix = path.slice(0..common_prefix_len);
    //                 let old_index = leaf.prefix.at(common_prefix_len);
    //                 let old_remainder = leaf.prefix.slice(common_prefix_len + 1..);
    //                 let new_index = path.at(common_prefix_len);
    //                 let new_remainder = path.slice(common_prefix_len + 1..);
    //                 let mut children = [const { None }; 16];
    //                 children[old_index as usize] = Some(Box::new(Self::Leaf(LeafNode::new(old_remainder, leaf.value))).into());
    //                 children[new_index as usize] = Some(Box::new(Self::Leaf(LeafNode::new(new_remainder, value))).into());
    //                 let new_branch = BranchNode::new(common_prefix, children);
    //                 new_branch.into()
    //             }
    //         }
    //         Self::Branch(mut branch) => {
    //             let common_prefix_len = path.common_prefix_length(&branch.prefix);

    //             if common_prefix_len == branch.prefix.len() {
    //                 if common_prefix_len == path.len() {
    //                     panic!("New value would be inserted at an existing branch node");
    //                 } else {
    //                     // insert into the appropriate child slot of the current branch
    //                     let child = TrieNode::<V>::from(mem::take(&mut branch.children[path.at(common_prefix_len) as usize]));
    //                     branch.children[path.at(common_prefix_len) as usize] = Some(Box::new(child.insert(path.slice(common_prefix_len + 1..), value)).into());
    //                     branch.into()
    //                 }
    //             } else {
    //                 // create a new branch at the common prefix
    //                 let common_prefix = path.slice(0..common_prefix_len);
    //                 let old_index = branch.prefix.at(common_prefix_len);
    //                 let old_remainder = branch.prefix.slice(common_prefix_len + 1..);
    //                 let new_index = path.at(common_prefix_len);
    //                 let new_remainder = path.slice(common_prefix_len + 1..);
    //                 let mut children = [const { None }; 16];
    //                 children[old_index as usize] = Some(Box::new(Self::Branch(branch.with_prefix(old_remainder))));
    //                 children[new_index as usize] = Some(Box::new(Self::Leaf(LeafNode::new(new_remainder, value))));
    //                 let new_branch = BranchNode::new(common_prefix, children);
    //                 new_branch.into()
    //             }
    //         }
    //     }
    // }

    // pub fn get(&self, path: Nibbles) -> Option<&V> {
    //     match self {
    //         Self::EmptyRoot => None,
    //         Self::Leaf(leaf) => {
    //             if leaf.prefix == path {
    //                 Some(&leaf.value)
    //             } else {
    //                 None
    //             }
    //         },
    //         Self::Branch(branch) => {
    //             let common_prefix_len = path.common_prefix_length(&branch.prefix);
    //             if common_prefix_len == branch.prefix.len() {
    //                 if common_prefix_len == path.len() {
    //                     panic!("Path resolves to a branch node, which should not happen");
    //                 } else {
    //                     let index = path.at(common_prefix_len);
    //                     let child = &branch.children[index as usize];
    //                     if let Some(child) = child {
    //                         child.get(path.slice(common_prefix_len + 1..))
    //                     } else {
    //                         None
    //                     }
    //                 }
    //             } else {
    //                 None
    //             }
    //         },
    //     }
    // }

    // pub fn remove(self, path: Nibbles) -> (Self, bool) {
    //     match self {
    //         Self::EmptyRoot => (Self::new_empty_root(), false),
    //         Self::Leaf(ref leaf) => {
    //             if leaf.prefix == path {
    //                 (Self::new_empty_root(), true)
    //             } else {
    //                 (self, false)
    //             }
    //         }
    //         Self::Branch(mut branch) => {
    //             let common_prefix_len = path.common_prefix_length(&branch.prefix);
    //             if common_prefix_len == branch.prefix.len() {
    //                 let index = path.at(common_prefix_len);
    //                 let child = TrieNode::<V>::from(mem::take(&mut branch.children[index as usize]));
    //                 let (child, removed) = child.remove(path.slice(common_prefix_len + 1..));
    //                 // only re-add the child if it's not an empty root
    //                 if !matches!(child, Self::EmptyRoot) {
    //                     branch.children[index as usize] = Some(Box::new(child));
    //                 }
    //                 if branch.num_children() == 1 {
    //                     // if the branch has only one child, remove this branch and extend the child's prefix with the branch's prefix
    //                     let mut idx = 0;
    //                     for (index, child) in branch.children.iter().enumerate() {
    //                         if child.is_some() {
    //                             idx = index;
    //                             break;
    //                         }
    //                     }
    //                     let child = TrieNode::<V>::from(mem::take(&mut branch.children[idx]));
    //                     let new_prefix = Nibbles::from_nibbles([branch.prefix, Nibbles::from_nibbles([idx as u8]), child.prefix()].concat());
    //                     let child = child.with_prefix(new_prefix);
    //                     return (child, removed);
    //                 } else {
    //                     (branch.into(), removed)
    //                 }
    //             } else {
    //                 (branch.into(), false)
    //             }
    //         }
    //     }
    // }

    fn prefix(&self) -> Nibbles {
        match self {
            Self::EmptyRoot => Nibbles::new(),
            Self::Leaf(leaf) => leaf.prefix.clone(),
            Self::Branch(branch) => branch.prefix.clone(),
        }
    }

    fn with_prefix(self, prefix: Nibbles) -> Self {
        match self {
            Self::EmptyRoot => panic!("Cannot set prefix on empty root"),
            Self::Leaf(leaf) => leaf.with_prefix(prefix).into(),
            Self::Branch(branch) => branch.with_prefix(prefix).into(),
        }
    }
}

impl<V: Value> From<Option<Box<TrieNode<V>>>> for TrieNode<V> {
    fn from(node: Option<Box<TrieNode<V>>>) -> Self {
        match node {
            Some(node) => *node,
            None => Self::new_empty_root(),
        }
    }
}

impl<V: Value> From<BranchNode> for TrieNode<V> {
    fn from(branch: BranchNode) -> Self {
        Self::Branch(branch)
    }
}

impl<V: Value> From<LeafNode<V>> for TrieNode<V> {
    fn from(leaf: LeafNode<V>) -> Self {
        Self::Leaf(leaf)
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_trie_insert() {
//         let mut trie = Trie::new(3);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 1);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x04]), 2);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x05]), 3);

//         assert_eq!(trie.root, BranchNode::new(Nibbles::from_nibbles(&[0x01, 0x02]), [
//             None, None, None, Some(Box::new(LeafNode::new(Nibbles::new(), 1).into())),
//             Some(Box::new(LeafNode::new(Nibbles::new(), 2).into())), Some(Box::new(LeafNode::new(Nibbles::new(), 3).into())), None, None,
//             None, None, None, None,
//             None, None, None, None]).into());

//         let mut trie = Trie::new(3);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 1);
//         trie.insert(Nibbles::from_nibbles(&[0x05, 0x02, 0x00]), 2);
//         trie.insert(Nibbles::from_nibbles(&[0x09, 0x02, 0x03]), 3);
//         trie.insert(Nibbles::from_nibbles(&[0x0d, 0x0a, 0x0b]), 4);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 5);
//         trie.insert(Nibbles::from_nibbles(&[0x05, 0x02, 0x00]), 6);

//         assert_eq!(trie.root, BranchNode::new(Nibbles::new(), [
//             None, Some(Box::new(LeafNode::new(Nibbles::from_nibbles(&[0x02, 0x03]), 5).into())), None, None,
//             None, Some(Box::new(LeafNode::new(Nibbles::from_nibbles(&[0x02, 0x00]), 6).into())), None, None,
//             None, Some(Box::new(LeafNode::new(Nibbles::from_nibbles(&[0x02, 0x03]), 3).into())), None, None,
//             None, Some(Box::new(LeafNode::new(Nibbles::from_nibbles(&[0x0a, 0x0b]), 4).into())), None, None]).into());

//         let mut trie = Trie::new(3);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 1);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x03, 0x03]), 2);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x04, 0x03]), 3);

//         assert_eq!(trie.root, BranchNode::new(Nibbles::from_nibbles(&[0x01]), [
//             None, None, Some(Box::new(LeafNode::new(Nibbles::from_nibbles(&[0x03]), 1).into())), Some(Box::new(LeafNode::new(Nibbles::from_nibbles(&[0x03]), 2).into())),
//             Some(Box::new(LeafNode::new(Nibbles::from_nibbles(&[0x03]), 3).into())), None, None, None,
//             None, None, None, None,
//             None, None, None, None]).into());

//         let mut trie = Trie::new(3);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 1);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x0f, 0x03]), 2);
//         trie.insert(Nibbles::from_nibbles(&[0x0f, 0x02, 0x03]), 3);

//         assert_eq!(trie.root, BranchNode::new(Nibbles::new(), [
//             None, Some(Box::new(BranchNode::new(Nibbles::new(), [
//                 None, None, Some(Box::new(LeafNode::new(Nibbles::from_nibbles(&[0x03]), 1).into())), None,
//                 None, None, None, None,
//                 None, None, None, None,
//                 None, None, None, Some(Box::new(LeafNode::new(Nibbles::from_nibbles(&[0x03]), 2).into()))]).into())), None, None,
//             None, None, None, None,
//             None, None, None, None,
//             None, None, None, Some(Box::new(LeafNode::new(Nibbles::from_nibbles(&[0x02, 0x03]), 3).into()))]).into());
//     }

//     #[test]
//     fn test_trie_get() {
//         let mut trie = Trie::new(3);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 1);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x04]), 2);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x05]), 3);

//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x03])), Some(&1));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x04])), Some(&2));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x05])), Some(&3));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x06])), None);

//         let mut trie = Trie::new(3);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 1);
//         trie.insert(Nibbles::from_nibbles(&[0x05, 0x02, 0x00]), 2);
//         trie.insert(Nibbles::from_nibbles(&[0x09, 0x02, 0x03]), 3);
//         trie.insert(Nibbles::from_nibbles(&[0x0d, 0x0a, 0x0b]), 4);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 5);
//         trie.insert(Nibbles::from_nibbles(&[0x05, 0x02, 0x00]), 6);

//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x03])), Some(&5));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x05, 0x02, 0x00])), Some(&6));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x09, 0x02, 0x03])), Some(&3));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x0d, 0x0a, 0x0b])), Some(&4));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x06])), None);

//         let mut trie = Trie::new(3);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 1);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x03, 0x03]), 2);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x04, 0x03]), 3);

//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x03])), Some(&1));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x03, 0x03])), Some(&2));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x04, 0x03])), Some(&3));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x05, 0x03])), None);

//         let mut trie = Trie::new(3);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 1);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x0f, 0x03]), 2);
//         trie.insert(Nibbles::from_nibbles(&[0x0f, 0x02, 0x03]), 3);

//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x03])), Some(&1));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x0f, 0x03])), Some(&2));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x0f, 0x02, 0x03])), Some(&3));
//         assert_eq!(trie.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x06])), None);
//     }

//     #[test]
//     fn test_trie_remove() {
//         let mut trie = Trie::new(3);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 1);
//         assert_eq!(trie.remove(Nibbles::from_nibbles(&[0x01, 0x02, 0x03])), true);
//         assert_eq!(trie.root, TrieNode::new_empty_root());

//         let mut trie = Trie::new(3);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 1);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x04]), 2);
//         assert_eq!(trie.remove(Nibbles::from_nibbles(&[0x01, 0x02, 0x03])), true);
//         assert_eq!(trie.root, LeafNode::new(Nibbles::from_nibbles(&[0x01, 0x02, 0x04]), 2).into());
//         assert_eq!(trie.remove(Nibbles::from_nibbles(&[0x01, 0x02, 0x04])), true);
//         assert_eq!(trie.root, TrieNode::new_empty_root());

//         let mut trie = Trie::new(3);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), 1);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x04]), 2);
//         trie.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x05]), 3);
//         assert_eq!(trie.remove(Nibbles::from_nibbles(&[0x01, 0x02, 0x03])), true);
//         assert_eq!(trie.root, BranchNode::new(Nibbles::from_nibbles(&[0x01, 0x02]), [
//             None, None, None, None,
//             Some(Box::new(LeafNode::new(Nibbles::new(), 2).into())), Some(Box::new(LeafNode::new(Nibbles::new(), 3).into())), None, None,
//             None, None, None, None,
//             None, None, None, None]).into());
//         assert_eq!(trie.remove(Nibbles::from_nibbles(&[0x01, 0x02, 0x04])), true);
//         assert_eq!(trie.root, LeafNode::new(Nibbles::from_nibbles(&[0x01, 0x02, 0x05]), 3).into());
//         assert_eq!(trie.remove(Nibbles::from_nibbles(&[0x01, 0x02, 0x05])), true);
//         assert_eq!(trie.root, TrieNode::new_empty_root());
//     }
// }
