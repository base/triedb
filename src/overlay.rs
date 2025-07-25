use crate::{
    node::{Node, TrieValue},
    pointer::Pointer,
};
use alloy_trie::Nibbles;

/// Mutable overlay state that accumulates changes during transaction building.
/// Changes are stored unsorted for fast insertion, then sorted when frozen.
#[derive(Debug, Clone, Default)]
pub struct OverlayStateMut {
    changes: Vec<(Nibbles, Option<TrieValue>)>,
}

impl OverlayStateMut {
    /// Creates a new empty mutable overlay state.
    pub fn new() -> Self {
        Self { changes: Vec::new() }
    }

    /// Creates a new mutable overlay state with the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self { changes: Vec::with_capacity(capacity) }
    }

    /// Inserts a change into the overlay state.
    /// Multiple changes to the same path will keep the latest value.
    pub fn insert(&mut self, path: Nibbles, value: Option<TrieValue>) {
        // For now, just append. We could optimize by checking for duplicates,
        // but the freeze operation will handle deduplication anyway.
        self.changes.push((path, value));
    }

    /// Returns the number of changes in the overlay.
    pub fn len(&self) -> usize {
        self.changes.len()
    }

    /// Returns true if the overlay is empty.
    pub fn is_empty(&self) -> bool {
        self.changes.is_empty()
    }

    /// Freezes the mutable overlay into an immutable sorted overlay.
    /// This sorts the changes and deduplicates by path, keeping the last value for each path.
    pub fn freeze(mut self) -> OverlayState {
        if self.changes.is_empty() {
            return OverlayState { changes: Vec::new().into_boxed_slice(), prefix_offset: 0 };
        }

        // Sort by path
        self.changes.sort_by(|a, b| a.0.cmp(&b.0));

        // Deduplicate by path, keeping the last occurrence of each path
        let mut deduped = Vec::with_capacity(self.changes.len());
        let mut last_path: Option<&Nibbles> = None;

        for (path, value) in &self.changes {
            if last_path != Some(path) {
                deduped.push((path.clone(), value.clone()));
                last_path = Some(path);
            } else {
                // Update the last entry with the newer value
                if let Some(last_entry) = deduped.last_mut() {
                    last_entry.1 = value.clone();
                }
            }
        }

        OverlayState { changes: deduped.into_boxed_slice(), prefix_offset: 0 }
    }
}

/// Immutable overlay state with sorted changes for efficient querying and sub-slicing.
/// This is created by freezing an OverlayStateMut and allows for efficient prefix operations.
#[derive(Debug, Clone)]
pub struct OverlayState {
    changes: Box<[(Nibbles, Option<TrieValue>)]>,
    prefix_offset: usize,
}

impl OverlayState {
    /// Creates an empty overlay state.
    pub fn empty() -> Self {
        Self { changes: Vec::new().into_boxed_slice(), prefix_offset: 0 }
    }

    /// Returns the number of changes in the overlay.
    pub fn len(&self) -> usize {
        self.changes.len()
    }

    /// Returns true if the overlay is empty.
    pub fn is_empty(&self) -> bool {
        self.changes.is_empty()
    }

    /// Looks up a specific path in the overlay.
    /// Returns Some(value) if found, None if not in overlay.
    /// The path is adjusted by the prefix_offset before lookup.
    pub fn lookup(&self, path: &Nibbles) -> Option<&Option<TrieValue>> {
        match self.changes.binary_search_by(|(p, _)| self.compare_with_offset(p, path)) {
            Ok(index) => Some(&self.changes[index].1),
            Err(_) => None,
        }
    }

    /// Finds all entries that have the given prefix.
    /// Returns a sub-slice of the overlay containing only matching entries.
    /// The prefix is compared against offset-adjusted paths.
    pub fn find_prefix_range(&self, prefix: &Nibbles) -> OverlayState {
        if self.changes.is_empty() {
            return OverlayState::empty();
        }

        let mut start_idx = None;
        let mut end_idx = self.changes.len();

        // Find the range of entries that start with the prefix after applying offset
        for (i, (path, _)) in self.changes.iter().enumerate() {
            if path.len() >= self.prefix_offset {
                let adjusted_path = path.slice(self.prefix_offset..);
                if adjusted_path.len() >= prefix.len() && adjusted_path[..prefix.len()] == *prefix {
                    if start_idx.is_none() {
                        start_idx = Some(i);
                    }
                } else if start_idx.is_some() {
                    // We've found the end of the matching range
                    end_idx = i;
                    break;
                }
            }
        }

        match start_idx {
            Some(start) => OverlayState {
                changes: self.changes[start..end_idx].to_vec().into_boxed_slice(),
                prefix_offset: self.prefix_offset,
            },
            None => OverlayState::empty(),
        }
    }

    /// Creates a new OverlayState with a prefix offset applied.
    /// This is used for storage trie traversal where we want to strip the account prefix (64
    /// nibbles) from all paths, effectively converting 128-nibble storage paths to 64-nibble
    /// storage-relative paths.
    ///
    /// # Panics
    ///
    /// Panics if the prefix offset would break the sort order. This happens when paths don't share
    /// a common prefix up to the offset length, which would cause the offset-adjusted paths to be
    /// out of order.
    pub fn with_prefix_offset(&self, offset: usize) -> OverlayState {
        let total_offset = self.prefix_offset + offset;

        // Validate that all paths share the same prefix up to total_offset
        // and that offset-adjusted paths maintain sort order
        if self.changes.len() > 1 {
            let first_path = &self.changes[0].0;
            let last_path = &self.changes[self.changes.len() - 1].0;

            // Check that both first and last paths are long enough
            if first_path.len() < total_offset || last_path.len() < total_offset {
                panic!(
                    "with_prefix_offset: offset {} would exceed path length (first: {}, last: {})",
                    total_offset,
                    first_path.len(),
                    last_path.len()
                );
            }

            // Check that first and last paths share the same prefix up to total_offset
            let first_prefix = first_path.slice(..total_offset);
            let last_prefix = last_path.slice(..total_offset);
            if first_prefix != last_prefix {
                panic!("with_prefix_offset: paths don't share common prefix up to offset {total_offset}\nfirst: {first_path:?}\nlast: {last_path:?}");
            }
        }

        OverlayState { changes: self.changes.clone(), prefix_offset: total_offset }
    }

    /// Helper method to compare a stored path with a target path, applying prefix_offset.
    /// Returns the comparison result of the offset-adjusted stored path vs target path.
    fn compare_with_offset(
        &self,
        stored_path: &Nibbles,
        target_path: &Nibbles,
    ) -> std::cmp::Ordering {
        if stored_path.len() < self.prefix_offset {
            std::cmp::Ordering::Less
        } else {
            let adjusted_path = stored_path.slice(self.prefix_offset..);
            adjusted_path.cmp(target_path)
        }
    }

    /// Creates a sub-slice of the overlay from the given range.
    /// This is useful for recursive traversal where we want to pass a subset
    /// of changes to child operations.
    pub fn sub_slice(&self, start: usize, end: usize) -> OverlayState {
        let end = end.min(self.changes.len());
        let start = start.min(end);

        OverlayState {
            changes: self.changes[start..end].to_vec().into_boxed_slice(),
            prefix_offset: self.prefix_offset,
        }
    }

    /// Creates a sub-slice containing only changes that come before the given prefix.
    /// The prefix comparison takes prefix_offset into account.
    pub fn sub_slice_before_prefix(&self, prefix: &Nibbles) -> OverlayState {
        let index = self
            .changes
            .binary_search_by(|(p, _)| self.compare_with_offset(p, prefix))
            .unwrap_or_else(|i| i); // Insert position is exactly what we want for "before"
        self.sub_slice(0, index)
    }

    /// Creates a sub-slice containing only changes that come strictly after the given prefix.
    /// The prefix comparison takes prefix_offset into account.
    pub fn sub_slice_after_prefix(&self, prefix: &Nibbles) -> OverlayState {
        // Find the next key after prefix by incrementing prefix
        let next_prefix = match prefix.increment() {
            Some(next) => next,
            None => {
                // Prefix is all 0xF's, nothing can come after it
                return OverlayState::empty();
            }
        };

        let index = self
            .changes
            .binary_search_by(|(p, _)| self.compare_with_offset(p, &next_prefix))
            .unwrap_or_else(|i| i);
        self.sub_slice(index, self.changes.len())
    }

    /// Creates a sub-slice containing only changes that affect the subtree
    /// rooted at the given path prefix. This is used during recursive trie traversal
    /// to filter overlay changes relevant to each subtree.
    pub fn sub_slice_for_prefix(&self, prefix: &Nibbles) -> OverlayState {
        self.find_prefix_range(prefix)
    }

    /// Returns an iterator over all changes in the overlay.
    /// The paths are adjusted by the prefix_offset.
    pub fn iter(&self) -> impl Iterator<Item = (Nibbles, &Option<TrieValue>)> {
        self.changes.iter().filter_map(move |(path, value)| {
            if path.len() >= self.prefix_offset {
                let adjusted_path = path.slice(self.prefix_offset..);
                Some((adjusted_path, value))
            } else {
                None
            }
        })
    }

    /// Checks if the overlay contains any changes that would affect the given path.
    /// This includes exact matches and any changes to descendants of the path.
    /// The path comparison takes prefix_offset into account.
    pub fn affects_path(&self, path: &Nibbles) -> bool {
        if self.is_empty() {
            return false;
        }

        // Check for exact match or any path that starts with the given path after applying offset
        self.iter().any(|(overlay_path, _)| overlay_path.starts_with(path))
    }
}

/// Pointer that can reference either on-disk nodes or in-memory overlay nodes.
/// This allows the trie traversal to seamlessly handle both persisted and overlayed state.
#[derive(Debug, Clone)]
pub enum OverlayPointer {
    /// Reference to a node stored on disk
    OnDisk(Pointer),
    /// Reference to a node stored in memory as part of the overlay
    InMemory(Box<Node>),
}

impl OverlayPointer {
    /// Creates a new on-disk overlay pointer.
    pub fn on_disk(pointer: Pointer) -> Self {
        Self::OnDisk(pointer)
    }

    /// Creates a new in-memory overlay pointer.
    pub fn in_memory(node: Node) -> Self {
        Self::InMemory(Box::new(node))
    }

    /// Returns true if this pointer references an on-disk node.
    pub fn is_on_disk(&self) -> bool {
        matches!(self, Self::OnDisk(_))
    }

    /// Returns true if this pointer references an in-memory node.
    pub fn is_in_memory(&self) -> bool {
        matches!(self, Self::InMemory(_))
    }

    /// Returns the underlying disk pointer if this is an on-disk reference.
    pub fn as_disk_pointer(&self) -> Option<&Pointer> {
        match self {
            Self::OnDisk(pointer) => Some(pointer),
            Self::InMemory(_) => None,
        }
    }

    /// Returns the underlying in-memory node if this is an in-memory reference.
    pub fn as_memory_node(&self) -> Option<&Node> {
        match self {
            Self::OnDisk(_) => None,
            Self::InMemory(node) => Some(node),
        }
    }

    /// Converts this overlay pointer to an owned Node.
    /// For on-disk pointers, this would require loading the node from storage.
    /// For in-memory pointers, this clones the existing node.
    pub fn into_node(self) -> Result<Node, OverlayError> {
        match self {
            Self::OnDisk(_) => Err(OverlayError::DiskNodeNotLoaded),
            Self::InMemory(node) => Ok(*node),
        }
    }
}

impl From<Pointer> for OverlayPointer {
    fn from(pointer: Pointer) -> Self {
        Self::OnDisk(pointer)
    }
}

impl From<Node> for OverlayPointer {
    fn from(node: Node) -> Self {
        Self::InMemory(Box::new(node))
    }
}

/// Errors that can occur when working with overlay pointers.
#[derive(Debug)]
pub enum OverlayError {
    /// Attempted to access a disk node without loading it first
    DiskNodeNotLoaded,
}

impl std::fmt::Display for OverlayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DiskNodeNotLoaded => write!(f, "disk node not loaded"),
        }
    }
}

impl std::error::Error for OverlayError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{account::Account, node::TrieValue};
    use alloy_primitives::U256;
    use alloy_trie::{Nibbles, EMPTY_ROOT_HASH, KECCAK_EMPTY};

    fn test_account() -> Account {
        Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY)
    }

    #[test]
    fn test_mutable_overlay_basic_operations() {
        let mut overlay = OverlayStateMut::new();
        assert!(overlay.is_empty());
        assert_eq!(overlay.len(), 0);

        let path1 = Nibbles::from_nibbles([1, 2, 3, 4]);
        let path2 = Nibbles::from_nibbles([5, 6, 7, 8]);
        let account = test_account();

        overlay.insert(path1.clone(), Some(TrieValue::Account(account.clone())));
        overlay.insert(path2.clone(), None); // Tombstone

        assert!(!overlay.is_empty());
        assert_eq!(overlay.len(), 2);
    }

    #[test]
    fn test_freeze_and_lookup() {
        let mut mutable = OverlayStateMut::new();
        let path1 = Nibbles::from_nibbles([1, 2, 3, 4]);
        let path2 = Nibbles::from_nibbles([5, 6, 7, 8]);
        let account = test_account();

        mutable.insert(path1.clone(), Some(TrieValue::Account(account.clone())));
        mutable.insert(path2.clone(), None);

        let frozen = mutable.freeze();

        assert_eq!(frozen.len(), 2);

        // Test lookup
        let result1 = frozen.lookup(&path1);
        assert!(result1.is_some());
        assert!(result1.unwrap().is_some());

        let result2 = frozen.lookup(&path2);
        assert!(result2.is_some());
        assert!(result2.unwrap().is_none()); // Tombstone

        let path3 = Nibbles::from_nibbles([9, 10, 11, 12]);
        let result3 = frozen.lookup(&path3);
        assert!(result3.is_none());
    }

    #[test]
    fn test_deduplication_on_freeze() {
        let mut mutable = OverlayStateMut::new();
        let path = Nibbles::from_nibbles([1, 2, 3, 4]);
        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // Insert multiple values for the same path
        mutable.insert(path.clone(), Some(TrieValue::Account(account1)));
        mutable.insert(path.clone(), Some(TrieValue::Account(account2.clone())));
        mutable.insert(path.clone(), None); // Tombstone should win

        let frozen = mutable.freeze();

        assert_eq!(frozen.len(), 1);
        let result = frozen.lookup(&path);
        assert!(result.is_some());
        assert!(result.unwrap().is_none()); // Should be the tombstone
    }

    #[test]
    fn test_prefix_range() {
        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        // Add some paths with common prefixes
        mutable
            .insert(Nibbles::from_nibbles([1, 2, 3, 4]), Some(TrieValue::Account(account.clone())));
        mutable
            .insert(Nibbles::from_nibbles([1, 2, 5, 6]), Some(TrieValue::Account(account.clone())));
        mutable
            .insert(Nibbles::from_nibbles([1, 3, 7, 8]), Some(TrieValue::Account(account.clone())));
        mutable
            .insert(Nibbles::from_nibbles([2, 3, 4, 5]), Some(TrieValue::Account(account.clone())));

        let frozen = mutable.freeze();

        // Find entries with prefix [1, 2]
        let prefix = Nibbles::from_nibbles([1, 2]);
        let subset = frozen.find_prefix_range(&prefix);

        assert_eq!(subset.len(), 2); // Should match first two entries

        // Find entries with prefix [1]
        let prefix = Nibbles::from_nibbles([1]);
        let subset = frozen.find_prefix_range(&prefix);

        assert_eq!(subset.len(), 3); // Should match first three entries
    }

    #[test]
    fn test_affects_path() {
        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        mutable
            .insert(Nibbles::from_nibbles([1, 2, 3, 4]), Some(TrieValue::Account(account.clone())));
        mutable
            .insert(Nibbles::from_nibbles([1, 2, 5, 6]), Some(TrieValue::Account(account.clone())));

        let frozen = mutable.freeze();

        // Test exact match
        assert!(frozen.affects_path(&Nibbles::from_nibbles([1, 2, 3, 4])));

        // Test parent path
        assert!(frozen.affects_path(&Nibbles::from_nibbles([1, 2])));

        // Test unrelated path
        assert!(!frozen.affects_path(&Nibbles::from_nibbles([7, 8, 9, 10])));
    }

    #[test]
    fn test_empty_overlay() {
        let empty_mutable = OverlayStateMut::new();
        let frozen = empty_mutable.freeze();

        assert!(frozen.is_empty());
        assert_eq!(frozen.len(), 0);

        let path = Nibbles::from_nibbles([1, 2, 3, 4]);
        assert!(frozen.lookup(&path).is_none());
        assert!(!frozen.affects_path(&path));

        let subset = frozen.find_prefix_range(&path);
        assert!(subset.is_empty());
    }

    #[test]
    fn test_overlay_pointer_creation() {
        use crate::{location::Location, node::Node, pointer::Pointer};
        use alloy_trie::{nodes::RlpNode, Nibbles, EMPTY_ROOT_HASH};

        // Test on-disk pointer
        let location = Location::for_cell(42);
        let rlp = RlpNode::word_rlp(&EMPTY_ROOT_HASH);
        let disk_pointer = Pointer::new(location, rlp);
        let overlay_pointer = OverlayPointer::on_disk(disk_pointer.clone());

        assert!(overlay_pointer.is_on_disk());
        assert!(!overlay_pointer.is_in_memory());
        assert_eq!(overlay_pointer.as_disk_pointer(), Some(&disk_pointer));
        assert!(overlay_pointer.as_memory_node().is_none());

        // Test in-memory pointer
        let path = Nibbles::from_nibbles([1, 2, 3, 4]);
        let account = test_account();
        let node = Node::new_leaf(path, &TrieValue::Account(account)).unwrap();
        let overlay_pointer = OverlayPointer::in_memory(node.clone());

        assert!(!overlay_pointer.is_on_disk());
        assert!(overlay_pointer.is_in_memory());
        assert!(overlay_pointer.as_disk_pointer().is_none());
        assert_eq!(overlay_pointer.as_memory_node(), Some(&node));
    }

    #[test]
    fn test_overlay_pointer_conversion() {
        use crate::{location::Location, pointer::Pointer};
        use alloy_trie::{nodes::RlpNode, Nibbles, EMPTY_ROOT_HASH};

        // Test From<Pointer>
        let location = Location::for_cell(42);
        let rlp = RlpNode::word_rlp(&EMPTY_ROOT_HASH);
        let disk_pointer = Pointer::new(location, rlp);
        let overlay_pointer: OverlayPointer = disk_pointer.into();
        assert!(overlay_pointer.is_on_disk());

        // Test From<Node>
        let path = Nibbles::from_nibbles([1, 2, 3, 4]);
        let account = test_account();
        let node = Node::new_leaf(path, &TrieValue::Account(account)).unwrap();
        let overlay_pointer: OverlayPointer = node.into();
        assert!(overlay_pointer.is_in_memory());
    }

    #[test]
    fn test_overlay_pointer_into_node() {
        use alloy_trie::Nibbles;

        // Test in-memory pointer
        let path = Nibbles::from_nibbles([1, 2, 3, 4]);
        let account = test_account();
        let original_node = Node::new_leaf(path, &TrieValue::Account(account)).unwrap();
        let overlay_pointer = OverlayPointer::in_memory(original_node.clone());

        let extracted_node = overlay_pointer.into_node().unwrap();
        assert_eq!(extracted_node.prefix(), original_node.prefix());
        assert_eq!(extracted_node.value().unwrap(), original_node.value().unwrap());

        // Test on-disk pointer (should fail)
        use crate::{location::Location, pointer::Pointer};
        use alloy_trie::{nodes::RlpNode, EMPTY_ROOT_HASH};

        let location = Location::for_cell(42);
        let rlp = RlpNode::word_rlp(&EMPTY_ROOT_HASH);
        let disk_pointer = Pointer::new(location, rlp);
        let overlay_pointer = OverlayPointer::on_disk(disk_pointer);

        assert!(overlay_pointer.into_node().is_err());
    }

    #[test]
    fn test_prefix_offset_functionality() {
        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        // Add paths that simulate account (64 nibbles) + storage slot (64 nibbles) = 128 nibbles
        // total Account path: [1, 2, 3, 4] (simulating first 4 nibbles of 64-nibble account
        // path) Storage paths extend the account path with storage slot nibbles
        let account_prefix = vec![1, 2, 3, 4];

        // Storage path 1: account + [5, 6]
        let mut storage_path1 = account_prefix.clone();
        storage_path1.extend([5, 6]);

        // Storage path 2: account + [7, 8]
        let mut storage_path2 = account_prefix.clone();
        storage_path2.extend([7, 8]);

        // Storage path 3: same account + [13, 14] (changed from different account to same account)
        let mut storage_path3 = account_prefix.clone();
        storage_path3.extend([13, 14]);

        mutable.insert(
            Nibbles::from_nibbles(storage_path1.clone()),
            Some(TrieValue::Account(account.clone())),
        );
        mutable.insert(
            Nibbles::from_nibbles(storage_path2.clone()),
            Some(TrieValue::Account(account.clone())),
        );
        mutable.insert(
            Nibbles::from_nibbles(storage_path3.clone()),
            Some(TrieValue::Account(account.clone())),
        );

        let frozen = mutable.freeze();

        // Test with prefix_offset = 4 (simulating stripping 4-nibble account prefix for 2-nibble
        // storage keys)
        let storage_overlay = frozen.with_prefix_offset(4);

        // Test lookup with offset
        let storage_key1 = Nibbles::from_nibbles([5, 6]); // Should find storage_path1
        let storage_key2 = Nibbles::from_nibbles([7, 8]); // Should find storage_path2
        let storage_key3 = Nibbles::from_nibbles([13, 14]); // Should find storage_path3
        let storage_key_missing = Nibbles::from_nibbles([15, 15]); // Should not find

        assert!(storage_overlay.lookup(&storage_key1).is_some());
        assert!(storage_overlay.lookup(&storage_key2).is_some());
        assert!(storage_overlay.lookup(&storage_key3).is_some());
        assert!(storage_overlay.lookup(&storage_key_missing).is_none());

        // Test iter with offset - should return offset-adjusted paths
        let iter_results: Vec<_> = storage_overlay.iter().collect();
        assert_eq!(iter_results.len(), 3);

        // The paths should be the storage-relative parts (after prefix_offset)
        let expected_paths = [
            Nibbles::from_nibbles([5, 6]),
            Nibbles::from_nibbles([7, 8]),
            Nibbles::from_nibbles([13, 14]),
        ];

        for (i, (path, _)) in iter_results.iter().enumerate() {
            assert_eq!(*path, expected_paths[i]);
        }
    }

    #[test]
    fn test_prefix_offset_sub_slice_methods() {
        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        // Create overlay with account-prefixed storage paths for a SINGLE account
        let _account_prefix = vec![1, 0, 0, 0]; // 4-nibble account prefix

        let paths = [
            vec![1, 0, 0, 0, 2, 0], // account + storage [2, 0]
            vec![1, 0, 0, 0, 5, 0], // account + storage [5, 0]
            vec![1, 0, 0, 0, 8, 0], // account + storage [8, 0]
            vec![1, 0, 0, 0, 9, 0], /* account + storage [9, 0] - changed from different account
                                     * to same account */
        ];

        for path in &paths {
            mutable.insert(
                Nibbles::from_nibbles(path.clone()),
                Some(TrieValue::Account(account.clone())),
            );
        }

        let frozen = mutable.freeze();
        let storage_overlay = frozen.with_prefix_offset(4); // Strip 4-nibble account prefix

        // Test sub_slice_before_prefix
        let split_point = Nibbles::from_nibbles([5, 0]); // Storage key [5, 0]
        let before = storage_overlay.sub_slice_before_prefix(&split_point);
        let after = storage_overlay.sub_slice_after_prefix(&split_point);

        // Before should contain storage keys [2, 0] (< [5, 0])
        assert_eq!(before.len(), 1);
        let before_paths: Vec<_> = before.iter().map(|(path, _)| path).collect();
        assert!(before_paths.contains(&Nibbles::from_nibbles([2, 0])));

        // After should contain storage keys [8, 0] and [9, 0] (strictly > [5, 0])
        assert_eq!(after.len(), 2);
        let after_paths: Vec<_> = after.iter().map(|(path, _)| path).collect();
        assert!(!after_paths.contains(&Nibbles::from_nibbles([5, 0]))); // Strictly after, so [5, 0] not included
        assert!(after_paths.contains(&Nibbles::from_nibbles([8, 0])));
        assert!(after_paths.contains(&Nibbles::from_nibbles([9, 0])));
    }

    #[test]
    fn test_prefix_offset_find_prefix_range() {
        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        // Create storage overlays for two different accounts
        let account1_prefix = vec![1, 0, 0, 0]; // Account 1: 4 nibbles
        let _account2_prefix = vec![2, 0, 0, 0]; // Account 2: 4 nibbles

        // Storage for account 1
        mutable.insert(
            Nibbles::from_nibbles([1, 0, 0, 0, 5, 5]),
            Some(TrieValue::Account(account.clone())),
        );
        mutable.insert(
            Nibbles::from_nibbles([1, 0, 0, 0, 5, 6]),
            Some(TrieValue::Account(account.clone())),
        );

        // Storage for account 2
        mutable.insert(
            Nibbles::from_nibbles([2, 0, 0, 0, 7, 7]),
            Some(TrieValue::Account(account.clone())),
        );

        let frozen = mutable.freeze();

        // Test finding storage for account 1 using find_prefix_range on original overlay
        let account1_storage =
            frozen.find_prefix_range(&Nibbles::from_nibbles(account1_prefix.clone()));
        assert_eq!(account1_storage.len(), 2);

        // Now test with prefix_offset - should convert to storage-relative paths
        let storage_overlay = account1_storage.with_prefix_offset(4);
        let storage_with_prefix5: Vec<_> = storage_overlay
            .find_prefix_range(&Nibbles::from_nibbles([5]))
            .iter()
            .map(|(path, _)| path)
            .collect();

        assert_eq!(storage_with_prefix5.len(), 2);
        assert!(storage_with_prefix5.contains(&Nibbles::from_nibbles([5, 5])));
        assert!(storage_with_prefix5.contains(&Nibbles::from_nibbles([5, 6])));
    }
}
