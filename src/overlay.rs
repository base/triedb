use crate::{
    account::Account,
    node::{Node, TrieValue},
    pointer::Pointer,
};
use alloy_primitives::{StorageValue, B256, U256};
use alloy_trie::Nibbles;
use std::sync::Arc;

#[derive(Debug, Clone)]
pub enum OverlayValue {
    Account(Account),
    Storage(StorageValue),
    Hash(B256),
}

impl TryFrom<OverlayValue> for TrieValue {
    type Error = &'static str;

    fn try_from(value: OverlayValue) -> Result<Self, Self::Error> {
        match value {
            OverlayValue::Account(account) => Ok(TrieValue::Account(account)),
            OverlayValue::Storage(storage) => Ok(TrieValue::Storage(storage)),
            OverlayValue::Hash(_) => Err("Cannot convert Hash overlay value to TrieValue"),
        }
    }
}

/// Mutable overlay state that accumulates changes during transaction building.
/// Changes are stored unsorted for fast insertion, then sorted when frozen.
#[derive(Debug, Clone, Default)]
pub struct OverlayStateMut {
    changes: Vec<(Nibbles, Option<OverlayValue>)>,
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
    pub fn insert(&mut self, path: Nibbles, value: Option<OverlayValue>) {
        // For now, just append. We could optimize by checking for duplicates,
        // but the freeze operation will handle deduplication anyway.

        match value {
            Some(OverlayValue::Storage(U256::ZERO)) => {
                // If the value is zero, this is actually a tombstone
                self.changes.push((path, None));
            }
            _ => {
                self.changes.push((path, value));
            }
        }
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
            return OverlayState { data: Arc::new([]), start_idx: 0, end_idx: 0, prefix_offset: 0 };
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

        let data: Arc<[(Nibbles, Option<OverlayValue>)]> = Arc::from(deduped.into_boxed_slice());
        let len = data.len();
        OverlayState { data, start_idx: 0, end_idx: len, prefix_offset: 0 }
    }
}

/// Immutable overlay state with sorted changes for efficient querying and zero-copy sub-slicing.
/// This is created by freezing an OverlayStateMut and allows for efficient prefix operations.
///
/// The overlay uses Arc-based storage for zero-copy sub-slicing and thread-safe sharing.
/// Sub-slices share the same underlying data and only track different bounds within it.
///
/// # Thread Safety
///
/// OverlayState is thread-safe and can be safely shared across threads. Multiple threads
/// can work with non-overlapping sub-slices simultaneously without any synchronization.
/// The Arc<[...]> provides thread-safe reference counting for the underlying data.
#[derive(Debug, Clone)]
pub struct OverlayState {
    data: Arc<[(Nibbles, Option<OverlayValue>)]>,
    start_idx: usize,
    end_idx: usize,
    prefix_offset: usize,
}

// SAFETY: OverlayState is thread-safe because:
// - Arc<[...]> provides thread-safe reference counting
// - All fields are immutable after construction
// - No interior mutability is used
// - All operations are read-only or create new instances
unsafe impl Send for OverlayState {}
unsafe impl Sync for OverlayState {}

impl OverlayState {
    /// Creates an empty overlay state.
    pub fn empty() -> Self {
        Self { data: Arc::new([]), start_idx: 0, end_idx: 0, prefix_offset: 0 }
    }

    #[cfg(test)]
    pub fn data(&self) -> &[(Nibbles, Option<OverlayValue>)] {
        &self.data
    }

    pub fn get(&self, index: usize) -> Option<(&[u8], &Option<OverlayValue>)> {
        let slice = self.effective_slice();
        if index < slice.len() {
            Some((&slice[index].0[self.prefix_offset..], &slice[index].1))
        } else {
            None
        }
    }

    #[inline]
    pub fn first(&self) -> Option<(&[u8], &Option<OverlayValue>)> {
        self.get(0)
    }

    /// Returns the effective slice of data for this overlay, respecting bounds.
    pub fn effective_slice(&self) -> &[(Nibbles, Option<OverlayValue>)] {
        &self.data[self.start_idx..self.end_idx]
    }

    /// Returns the number of changes in the overlay.
    pub fn len(&self) -> usize {
        self.end_idx - self.start_idx
    }

    /// Returns true if the overlay is empty.
    pub fn is_empty(&self) -> bool {
        self.start_idx >= self.end_idx
    }

    /// Looks up a specific path in the overlay.
    /// Returns Some(value) if found, None if not in overlay.
    /// The path is adjusted by the prefix_offset before lookup.
    pub fn lookup(&self, path: &[u8]) -> Option<&Option<OverlayValue>> {
        let slice = self.effective_slice();
        match slice.binary_search_by(|(p, _)| self.compare_with_offset(p, path)) {
            Ok(index) => Some(&slice[index].1),
            Err(_) => None,
        }
    }

    /// Finds all entries that have the given prefix.
    /// Returns a zero-copy sub-slice of the overlay containing only matching entries.
    /// The prefix is compared against offset-adjusted paths.
    pub fn find_prefix_range(&self, prefix: &[u8]) -> OverlayState {
        if self.is_empty() {
            return OverlayState::empty();
        }

        let slice = self.effective_slice();
        let mut start_idx = None;
        let mut end_idx = slice.len();

        // Find the range of entries that start with the prefix after applying offset
        for (i, (path, _)) in slice.iter().enumerate() {
            if path.len() >= self.prefix_offset {
                let adjusted_path = &path.as_slice()[self.prefix_offset..];
                if adjusted_path.len() >= prefix.len() &&
                    adjusted_path[..prefix.len()] == prefix[..]
                {
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
                data: Arc::clone(&self.data),
                start_idx: self.start_idx + start,
                end_idx: self.start_idx + end_idx,
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
        if self.len() > 1 {
            let slice = self.effective_slice();
            let first_path = &slice[0].0;
            let last_path = &slice[slice.len() - 1].0;

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

        OverlayState {
            data: Arc::clone(&self.data),
            start_idx: self.start_idx,
            end_idx: self.end_idx,
            prefix_offset: total_offset,
        }
    }

    /// Helper method to compare a stored path with a target path, applying prefix_offset.
    /// Returns the comparison result of the offset-adjusted stored path vs target path.
    fn compare_with_offset(&self, stored_path: &[u8], target_path: &[u8]) -> std::cmp::Ordering {
        if stored_path.len() < self.prefix_offset {
            std::cmp::Ordering::Less
        } else {
            let adjusted_path = &stored_path[self.prefix_offset..];
            adjusted_path.cmp(target_path)
        }
    }

    /// Creates a zero-copy sub-slice of the overlay from the given range.
    /// This is useful for recursive traversal where we want to pass a subset
    /// of changes to child operations without copying data.
    ///
    /// # Performance
    ///
    /// This operation is O(1) and creates no allocations. The returned OverlayState
    /// shares the same underlying Arc<[...]> data and only tracks different bounds.
    /// Perfect for thread pool scenarios where each thread processes a disjoint range.
    pub fn sub_slice(&self, start: usize, end: usize) -> OverlayState {
        let current_len = self.len();
        let end = end.min(current_len);
        let start = start.min(end);

        OverlayState {
            data: Arc::clone(&self.data),
            start_idx: self.start_idx + start,
            end_idx: self.start_idx + end,
            prefix_offset: self.prefix_offset,
        }
    }

    /// Partitions the overlay into three slices:
    /// - before: all changes before the prefix
    /// - with_prefix: all changes with the prefix
    /// - after: all changes after the prefix
    pub fn sub_slice_by_prefix(
        &self,
        prefix: &Nibbles,
    ) -> (OverlayState, OverlayState, OverlayState) {
        let slice = self.effective_slice();

        let start_index = slice
            .binary_search_by(|(p, _)| self.compare_with_offset(p, prefix))
            .unwrap_or_else(|i| i);
        let end_index = match prefix.increment() {
            Some(next) => slice
                .binary_search_by(|(p, _)| self.compare_with_offset(p, &next))
                .unwrap_or_else(|i| i),
            None => {
                // Prefix is all 0xF's, nothing can come after it
                slice.len()
            }
        };

        let before = self.sub_slice(0, start_index);
        let with_prefix = self.sub_slice(start_index, end_index);
        let after = self.sub_slice(end_index, slice.len());
        (before, with_prefix, after)
    }

    /// Creates a zero-copy sub-slice containing only changes that affect the subtree
    /// rooted at the given path prefix. This is used during recursive trie traversal
    /// to filter overlay changes relevant to each subtree.
    pub fn sub_slice_for_prefix(&self, prefix: &[u8]) -> OverlayState {
        self.find_prefix_range(prefix)
    }

    /// Returns an iterator over all changes in the overlay, respecting slice bounds.
    /// The paths are adjusted by the prefix_offset.
    pub fn iter(&self) -> impl Iterator<Item = (&[u8], &Option<OverlayValue>)> {
        self.effective_slice().iter().filter_map(move |(path, value)| {
            if path.len() > self.prefix_offset {
                let adjusted_path = &path.as_slice()[self.prefix_offset..];
                Some((adjusted_path, value))
            } else {
                None
            }
        })
    }

    pub fn contains_prefix_of(&self, path: &[u8]) -> bool {
        // Check for exact match or any path that starts with the given path after applying offset
        self.iter().any(|(overlay_path, _)| path.starts_with(overlay_path))
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

        overlay.insert(path1.clone(), Some(OverlayValue::Account(account.clone())));
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

        mutable.insert(path1.clone(), Some(OverlayValue::Account(account.clone())));
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
        mutable.insert(path.clone(), Some(OverlayValue::Account(account1)));
        mutable.insert(path.clone(), Some(OverlayValue::Account(account2.clone())));
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
        mutable.insert(
            Nibbles::from_nibbles([1, 2, 3, 4]),
            Some(OverlayValue::Account(account.clone())),
        );
        mutable.insert(
            Nibbles::from_nibbles([1, 2, 5, 6]),
            Some(OverlayValue::Account(account.clone())),
        );
        mutable.insert(
            Nibbles::from_nibbles([1, 3, 7, 8]),
            Some(OverlayValue::Account(account.clone())),
        );
        mutable.insert(
            Nibbles::from_nibbles([2, 3, 4, 5]),
            Some(OverlayValue::Account(account.clone())),
        );

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
    fn test_contains_prefix_of() {
        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        mutable.insert(
            Nibbles::from_nibbles([1, 2, 3, 4]),
            Some(OverlayValue::Account(account.clone())),
        );
        mutable.insert(
            Nibbles::from_nibbles([1, 2, 5, 6]),
            Some(OverlayValue::Account(account.clone())),
        );

        let frozen = mutable.freeze();

        // Test exact match
        assert!(frozen.contains_prefix_of(&[1, 2, 3, 4]));
        assert!(frozen.contains_prefix_of(&[1, 2, 5, 6]));

        // Test child path
        assert!(frozen.contains_prefix_of(&[1, 2, 3, 4, 5]));
        assert!(frozen.contains_prefix_of(&[1, 2, 5, 6, 15, 14, 13, 12]));

        // Test parent path
        assert!(!frozen.contains_prefix_of(&[1, 2]));
        assert!(!frozen.contains_prefix_of(&[1, 2, 3]));
        assert!(!frozen.contains_prefix_of(&[1, 2, 5]));

        // Test unrelated path
        assert!(!frozen.contains_prefix_of(&[7, 8, 9, 10]));
    }

    #[test]
    fn test_empty_overlay() {
        let empty_mutable = OverlayStateMut::new();
        let frozen = empty_mutable.freeze();

        assert!(frozen.is_empty());
        assert_eq!(frozen.len(), 0);

        let path = Nibbles::from_nibbles([1, 2, 3, 4]);
        assert!(frozen.lookup(&path).is_none());
        assert!(!frozen.contains_prefix_of(&path));

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
            Some(OverlayValue::Account(account.clone())),
        );
        mutable.insert(
            Nibbles::from_nibbles(storage_path2.clone()),
            Some(OverlayValue::Account(account.clone())),
        );
        mutable.insert(
            Nibbles::from_nibbles(storage_path3.clone()),
            Some(OverlayValue::Account(account.clone())),
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
            assert_eq!(*path, expected_paths[i].as_slice());
        }
    }

    #[test]
    fn test_prefix_offset_sub_slice_methods() {
        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        // Create overlay with account-prefixed storage paths for a SINGLE account
        let _account_prefix = [1, 0, 0, 0]; // 4-nibble account prefix

        let paths = [
            [1, 0, 0, 0, 2, 0], // account + storage [2, 0]
            [1, 0, 0, 0, 5, 0], // account + storage [5, 0]
            [1, 0, 0, 0, 8, 0], // account + storage [8, 0]
            [1, 0, 0, 0, 9, 0], // account + storage [9, 0]
        ];

        for path in &paths {
            mutable
                .insert(Nibbles::from_nibbles(*path), Some(OverlayValue::Account(account.clone())));
        }

        let frozen = mutable.freeze();
        let storage_overlay = frozen.with_prefix_offset(4); // Strip 4-nibble account prefix

        // Test sub_slice_before_prefix
        let split_point = Nibbles::from_nibbles([5, 0]); // Storage key [5, 0]

        let (before, with_prefix, after) = storage_overlay.sub_slice_by_prefix(&split_point);

        // Before should contain storage keys [2, 0] (< [5, 0])
        assert_eq!(before.len(), 1);
        let before_paths: Vec<_> = before.iter().map(|(path, _)| path).collect();
        assert!(before_paths.contains(&[2, 0].as_slice()));

        // With prefix should contain storage keys [5, 0]
        assert_eq!(with_prefix.len(), 1);
        let with_prefix_paths: Vec<_> = with_prefix.iter().map(|(path, _)| path).collect();
        assert!(with_prefix_paths.contains(&[5, 0].as_slice()));

        // After should contain storage keys [8, 0] and [9, 0] (strictly > [5, 0])
        assert_eq!(after.len(), 2);
        let after_paths: Vec<_> = after.iter().map(|(path, _)| path).collect();
        assert!(!after_paths.contains(&[5, 0].as_slice())); // Strictly after, so [5, 0] not included
        assert!(after_paths.contains(&[8, 0].as_slice()));
        assert!(after_paths.contains(&[9, 0].as_slice()));
    }

    #[test]
    fn test_prefix_offset_find_prefix_range() {
        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        // Create storage overlays for two different accounts
        let account1_prefix = [1, 0, 0, 0]; // Account 1: 4 nibbles
        let _account2_prefix = [2, 0, 0, 0]; // Account 2: 4 nibbles

        // Storage for account 1
        mutable.insert(
            Nibbles::from_nibbles([1, 0, 0, 0, 5, 5]),
            Some(OverlayValue::Account(account.clone())),
        );
        mutable.insert(
            Nibbles::from_nibbles([1, 0, 0, 0, 5, 6]),
            Some(OverlayValue::Account(account.clone())),
        );

        // Storage for account 2
        mutable.insert(
            Nibbles::from_nibbles([2, 0, 0, 0, 7, 7]),
            Some(OverlayValue::Account(account.clone())),
        );

        let frozen = mutable.freeze();

        // Test finding storage for account 1 using find_prefix_range on original overlay
        let account1_storage = frozen.find_prefix_range(&Nibbles::from_nibbles(account1_prefix));
        assert_eq!(account1_storage.len(), 2);

        // Now test with prefix_offset - should convert to storage-relative paths
        let storage_overlay = account1_storage.with_prefix_offset(4);
        let storage_with_prefix5 = storage_overlay.find_prefix_range(&Nibbles::from_nibbles([5]));

        assert_eq!(storage_with_prefix5.len(), 2);
        assert!(storage_with_prefix5.iter().any(|(path, _)| path == [5, 5].as_slice()));
        assert!(storage_with_prefix5.iter().any(|(path, _)| path == [5, 6].as_slice()));
    }

    #[test]
    fn test_zero_copy_sub_slicing() {
        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        // Add multiple entries
        for i in 0..10 {
            mutable.insert(
                Nibbles::from_nibbles([i, 0, 0, 0]),
                Some(OverlayValue::Account(account.clone())),
            );
        }

        let frozen = mutable.freeze();
        assert_eq!(frozen.len(), 10);

        // Create sub-slices
        let first_half = frozen.sub_slice(0, 5);
        let second_half = frozen.sub_slice(5, 10);
        let middle = frozen.sub_slice(2, 8);

        // Verify lengths
        assert_eq!(first_half.len(), 5);
        assert_eq!(second_half.len(), 5);
        assert_eq!(middle.len(), 6);

        // Verify they share the same Arc (same pointer)
        assert!(std::ptr::eq(frozen.data.as_ptr(), first_half.data.as_ptr()));
        assert!(std::ptr::eq(frozen.data.as_ptr(), second_half.data.as_ptr()));
        assert!(std::ptr::eq(frozen.data.as_ptr(), middle.data.as_ptr()));

        // Test recursive sub-slicing
        let sub_sub = middle.sub_slice(1, 4);
        assert_eq!(sub_sub.len(), 3);
        assert!(std::ptr::eq(frozen.data.as_ptr(), sub_sub.data.as_ptr()));

        // Verify bounds are correct
        assert_eq!(sub_sub.start_idx, 3); // middle starts at 2, +1 = 3
        assert_eq!(sub_sub.end_idx, 6); // middle starts at 2, +4 = 6
    }

    #[test]
    fn test_thread_safety_with_arc() {
        use std::thread;

        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        // Add entries
        for i in 0..100 {
            mutable.insert(
                Nibbles::from_nibbles([i % 16, (i / 16) % 16, 0, 0]),
                Some(OverlayValue::Account(account.clone())),
            );
        }

        let frozen = mutable.freeze();
        let shared_overlay = Arc::new(frozen);

        // Spawn multiple threads that work with different sub-slices
        let handles: Vec<_> = (0..4)
            .map(|i| {
                let overlay = Arc::clone(&shared_overlay);
                thread::spawn(move || {
                    let start = i * 25;
                    let end = (i + 1) * 25;
                    let sub_slice = overlay.sub_slice(start, end);

                    // Each thread verifies its slice
                    assert_eq!(sub_slice.len(), 25);

                    // Count entries (just to do some work)
                    let count = sub_slice.iter().count();
                    assert_eq!(count, 25);

                    count
                })
            })
            .collect();

        // Wait for all threads and collect results
        let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        assert_eq!(results, vec![25, 25, 25, 25]);
    }

    #[test]
    fn test_sub_slice_by_prefix() {
        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        // Create a diverse set of paths to test prefix partitioning
        // Use vectors instead of arrays to avoid size mismatch issues
        let test_paths = [
            // Before prefix [1, 2]
            (vec![0, 5, 6, 7], Some(OverlayValue::Account(account.clone()))),
            (vec![1, 0, 0, 0], Some(OverlayValue::Account(account.clone()))),
            (vec![1, 1, 9, 9], Some(OverlayValue::Account(account.clone()))),
            // Exact prefix [1, 2] and extensions
            (vec![1, 2], Some(OverlayValue::Account(account.clone()))),
            (vec![1, 2, 3, 4], Some(OverlayValue::Account(account.clone()))),
            (vec![1, 2, 5, 6], Some(OverlayValue::Account(account.clone()))),
            (vec![1, 2, 7, 8], None), // Tombstone with prefix
            // After prefix [1, 2]
            (vec![1, 3, 0, 0], Some(OverlayValue::Account(account.clone()))),
            (vec![2, 0, 0, 0], Some(OverlayValue::Account(account.clone()))),
            (vec![5, 5, 5, 5], Some(OverlayValue::Account(account.clone()))),
        ];

        for (path_nibbles, value) in test_paths.iter() {
            let path = Nibbles::from_nibbles(path_nibbles.clone());
            mutable.insert(path, value.clone());
        }

        let frozen = mutable.freeze();
        let prefix = Nibbles::from_nibbles([1, 2]);

        // Test sub_slice_by_prefix
        let (before, with_prefix, after) = frozen.sub_slice_by_prefix(&prefix);

        // Verify before slice - should contain paths < [1, 2]
        assert_eq!(before.len(), 3);
        let before_paths: Vec<_> = before.iter().map(|(path, _)| path).collect();
        assert!(before_paths.contains(&[0, 5, 6, 7].as_slice()));
        assert!(before_paths.contains(&[1, 0, 0, 0].as_slice()));
        assert!(before_paths.contains(&[1, 1, 9, 9].as_slice()));

        // Verify with_prefix slice - should contain paths that start with [1, 2]
        assert_eq!(with_prefix.len(), 4);
        let with_prefix_paths: Vec<_> = with_prefix.iter().map(|(path, _)| path).collect();
        assert!(with_prefix_paths.contains(&[1, 2].as_slice()));
        assert!(with_prefix_paths.contains(&[1, 2, 3, 4].as_slice()));
        assert!(with_prefix_paths.contains(&[1, 2, 5, 6].as_slice()));
        assert!(with_prefix_paths.contains(&[1, 2, 7, 8].as_slice()));

        // Verify after slice - should contain paths > [1, 2, ...] range
        assert_eq!(after.len(), 3);
        let after_paths: Vec<_> = after.iter().map(|(path, _)| path).collect();
        assert!(after_paths.contains(&[1, 3, 0, 0].as_slice()));
        assert!(after_paths.contains(&[2, 0, 0, 0].as_slice()));
        assert!(after_paths.contains(&[5, 5, 5, 5].as_slice()));

        // Verify that all slices together contain all original entries
        assert_eq!(before.len() + with_prefix.len() + after.len(), frozen.len());

        // Test with empty overlay
        let empty_frozen = OverlayStateMut::new().freeze();
        let (empty_before, empty_with, empty_after) = empty_frozen.sub_slice_by_prefix(&prefix);
        assert!(empty_before.is_empty());
        assert!(empty_with.is_empty());
        assert!(empty_after.is_empty());

        // Test with prefix that doesn't match anything
        let no_match_prefix = Nibbles::from_nibbles([9, 9, 9]);
        let (no_before, no_with, no_after) = frozen.sub_slice_by_prefix(&no_match_prefix);
        assert_eq!(no_before.len(), frozen.len()); // All entries should be "before"
        assert!(no_with.is_empty());
        assert!(no_after.is_empty());

        // Test edge case: prefix with all 0xF's (should handle increment() returning None)
        let max_prefix = Nibbles::from_nibbles([0xF, 0xF]);
        let (max_before, max_with, max_after) = frozen.sub_slice_by_prefix(&max_prefix);
        // All our test entries should be before 0xFF
        assert_eq!(max_before.len(), frozen.len());
        assert!(max_with.is_empty());
        assert!(max_after.is_empty());
    }

    #[test]
    fn test_sub_slice_by_prefix_with_exact_matches() {
        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        // Test case where we have exact prefix matches and no extensions
        let prefix = Nibbles::from_nibbles([2, 3]);

        mutable.insert(Nibbles::from_nibbles([1, 9]), Some(OverlayValue::Account(account.clone())));
        mutable.insert(Nibbles::from_nibbles([2, 2]), Some(OverlayValue::Account(account.clone())));
        mutable.insert(prefix.clone(), Some(OverlayValue::Account(account.clone()))); // Exact match
        mutable.insert(Nibbles::from_nibbles([2, 4]), Some(OverlayValue::Account(account.clone())));
        mutable.insert(Nibbles::from_nibbles([3, 0]), Some(OverlayValue::Account(account.clone())));

        let frozen = mutable.freeze();
        let (before, with_prefix, after) = frozen.sub_slice_by_prefix(&prefix);

        assert_eq!(before.len(), 2); // [1,9] and [2,2]
        assert_eq!(with_prefix.len(), 1); // [2,3] exactly
        assert_eq!(after.len(), 2); // [2,4] and [3,0]

        // Verify the exact match is in with_prefix
        let with_prefix_paths: Vec<_> = with_prefix.iter().map(|(path, _)| path).collect();
        assert!(with_prefix_paths.contains(&prefix.as_slice()));
    }

    #[test]
    fn test_sub_slice_by_prefix_with_prefix_offset() {
        let mut mutable = OverlayStateMut::new();
        let account = test_account();

        // Create paths that simulate account (4 nibbles) + storage (4 nibbles) patterns
        let _account_prefix = [1, 0, 0, 0];

        // Storage paths for the same account
        let storage_paths = [
            [1, 0, 0, 0, 2, 0, 0, 0], // account + storage [2,0,0,0]
            [1, 0, 0, 0, 5, 0, 0, 0], // account + storage [5,0,0,0]
            [1, 0, 0, 0, 5, 1, 0, 0], // account + storage [5,1,0,0]
            [1, 0, 0, 0, 8, 0, 0, 0], // account + storage [8,0,0,0]
        ];

        for path in storage_paths.iter() {
            mutable
                .insert(Nibbles::from_nibbles(path), Some(OverlayValue::Account(account.clone())));
        }

        let frozen = mutable.freeze();

        // Apply prefix offset to strip the account prefix
        let storage_overlay = frozen.with_prefix_offset(4);

        // Test partitioning by storage prefix [5]
        let storage_prefix = Nibbles::from_nibbles([5]);
        let (before, with_prefix, after) = storage_overlay.sub_slice_by_prefix(&storage_prefix);

        // Before should contain [2,0,0,0]
        assert_eq!(before.len(), 1);
        let before_paths: Vec<_> = before.iter().map(|(path, _)| path).collect();
        assert!(before_paths.contains(&[2, 0, 0, 0].as_slice()));

        // With prefix should contain [5,0,0,0] and [5,1,0,0]
        assert_eq!(with_prefix.len(), 2);
        let with_prefix_paths: Vec<_> = with_prefix.iter().map(|(path, _)| path).collect();
        assert!(with_prefix_paths.contains(&[5, 0, 0, 0].as_slice()));
        assert!(with_prefix_paths.contains(&[5, 1, 0, 0].as_slice()));

        // After should contain [8,0,0,0]
        assert_eq!(after.len(), 1);
        let after_paths: Vec<_> = after.iter().map(|(path, _)| path).collect();
        assert!(after_paths.contains(&[8, 0, 0, 0].as_slice()));
    }
}
