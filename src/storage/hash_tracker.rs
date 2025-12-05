//! Tracking infrastructure for parallel hash computation.
//!
//! The [`HashTracker`] collects nodes that need hash computation during an unhashed write
//! operation, organizing them by depth-from-leaf to enable level-based parallel hashing.

use crate::page::PageId;
use fxhash::FxHashMap;

/// Reference to a node in the trie, identified by its page and cell index.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeRef {
    /// The page containing the node.
    pub page_id: PageId,
    /// The cell index within the page.
    pub cell_index: u8,
}

impl NodeRef {
    /// Creates a new [`NodeRef`] from a page ID and cell index.
    pub fn new(page_id: PageId, cell_index: u8) -> Self {
        Self { page_id, cell_index }
    }
}

/// Metadata for a node requiring hash computation.
#[derive(Debug, Clone)]
pub struct UnhashedNode {
    /// Location of this node.
    pub node_ref: NodeRef,
    /// Parent node (None if this is root).
    pub parent: Option<NodeRef>,
    /// Which child slot in the parent (0-15 for Branch, 0 for AccountLeaf storage).
    pub parent_child_index: u8,
}

/// Tracks all nodes needing hash computation, organized by depth-from-leaf.
///
/// Depth 0 = leaves (no unhashed children), higher depths = closer to root.
/// This organization enables level-based parallel hashing: process all depth-0
/// nodes first, then depth-1, etc.
#[derive(Debug)]
pub struct HashTracker {
    /// Nodes grouped by depth: index 0 = leaves, higher indices = closer to root.
    by_depth: Vec<Vec<UnhashedNode>>,
    /// Quick lookup: NodeRef -> (depth, index within depth vector).
    node_index: FxHashMap<NodeRef, (u16, usize)>,
    /// Maximum depth recorded.
    max_depth: u16,
}

impl Default for HashTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl HashTracker {
    /// Creates a new empty [`HashTracker`].
    pub fn new() -> Self {
        Self {
            by_depth: Vec::new(),
            node_index: FxHashMap::default(),
            max_depth: 0,
        }
    }

    /// Creates a new [`HashTracker`] with pre-allocated capacity.
    ///
    /// For large batches, this avoids reallocations during recording.
    /// Estimate: ~12 nodes per change path on average (account + storage depth).
    pub fn with_capacity(num_changes: usize) -> Self {
        let estimated = num_changes * 12;
        Self {
            by_depth: Vec::with_capacity(20), // Typical max depth
            node_index: FxHashMap::with_capacity_and_hasher(estimated, Default::default()),
            max_depth: 0,
        }
    }

    /// Records an unhashed node at the given depth. Idempotent.
    ///
    /// Depth is computed during traversal: leaves = 0, parent = max(child depths) + 1.
    /// This allows level-based parallel hashing: process all depth-0 nodes, then depth-1, etc.
    ///
    /// Returns `true` if the node was newly recorded, `false` if already tracked.
    pub fn record(
        &mut self,
        node_ref: NodeRef,
        parent: Option<NodeRef>,
        parent_child_index: u8,
        depth: u16,
    ) -> bool {
        if self.node_index.contains_key(&node_ref) {
            return false; // Already recorded
        }

        // Ensure we have enough depth levels
        while self.by_depth.len() <= depth as usize {
            self.by_depth.push(Vec::new());
        }

        let idx = self.by_depth[depth as usize].len();
        self.by_depth[depth as usize].push(UnhashedNode {
            node_ref,
            parent,
            parent_child_index,
        });
        self.node_index.insert(node_ref, (depth, idx));
        self.max_depth = self.max_depth.max(depth);
        true
    }

    /// Returns nodes at given depth (for parallel processing).
    pub fn nodes_at_depth(&self, depth: u16) -> &[UnhashedNode] {
        self.by_depth
            .get(depth as usize)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Returns the maximum depth (root level).
    pub fn max_depth(&self) -> u16 {
        self.max_depth
    }

    /// Returns the total number of tracked nodes.
    pub fn len(&self) -> usize {
        self.by_depth.iter().map(|v| v.len()).sum()
    }

    /// Returns `true` if no nodes are tracked.
    pub fn is_empty(&self) -> bool {
        self.node_index.is_empty()
    }

    /// Clears all tracked nodes, keeping allocated capacity.
    pub fn clear(&mut self) {
        for level in &mut self.by_depth {
            level.clear();
        }
        self.node_index.clear();
        self.max_depth = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_page_id(n: u32) -> PageId {
        PageId::new(n).unwrap()
    }

    #[test]
    fn test_empty_tracker() {
        let tracker = HashTracker::new();
        assert!(tracker.is_empty());
        assert_eq!(tracker.len(), 0);
        assert_eq!(tracker.max_depth(), 0);
        assert!(tracker.nodes_at_depth(0).is_empty());
    }

    #[test]
    fn test_record_single_leaf() {
        let mut tracker = HashTracker::new();
        let node_ref = NodeRef::new(test_page_id(1), 0);

        assert!(tracker.record(node_ref, None, 0, 0));
        assert!(!tracker.is_empty());
        assert_eq!(tracker.len(), 1);
        assert_eq!(tracker.max_depth(), 0);

        let nodes = tracker.nodes_at_depth(0);
        assert_eq!(nodes.len(), 1);
        assert_eq!(nodes[0].node_ref, node_ref);
        assert!(nodes[0].parent.is_none());
    }

    #[test]
    fn test_record_idempotent() {
        let mut tracker = HashTracker::new();
        let node_ref = NodeRef::new(test_page_id(1), 0);

        assert!(tracker.record(node_ref, None, 0, 0));
        assert!(!tracker.record(node_ref, None, 0, 0)); // Second record returns false
        assert_eq!(tracker.len(), 1);
    }

    #[test]
    fn test_record_with_parent() {
        let mut tracker = HashTracker::new();
        let leaf = NodeRef::new(test_page_id(1), 0);
        let parent = NodeRef::new(test_page_id(1), 1);

        // Record leaf at depth 0
        tracker.record(leaf, Some(parent), 5, 0);
        // Record parent at depth 1
        tracker.record(parent, None, 0, 1);

        assert_eq!(tracker.len(), 2);
        assert_eq!(tracker.max_depth(), 1);

        let leaves = tracker.nodes_at_depth(0);
        assert_eq!(leaves.len(), 1);
        assert_eq!(leaves[0].parent, Some(parent));
        assert_eq!(leaves[0].parent_child_index, 5);

        let parents = tracker.nodes_at_depth(1);
        assert_eq!(parents.len(), 1);
        assert!(parents[0].parent.is_none());
    }

    #[test]
    fn test_multiple_depths() {
        let mut tracker = HashTracker::with_capacity(10);

        // Create a chain: leaf -> branch -> root
        let leaf = NodeRef::new(test_page_id(1), 0);
        let branch = NodeRef::new(test_page_id(1), 1);
        let root = NodeRef::new(test_page_id(1), 2);

        tracker.record(leaf, Some(branch), 3, 0);
        tracker.record(branch, Some(root), 7, 1);
        tracker.record(root, None, 0, 2);

        assert_eq!(tracker.len(), 3);
        assert_eq!(tracker.max_depth(), 2);

        assert_eq!(tracker.nodes_at_depth(0).len(), 1);
        assert_eq!(tracker.nodes_at_depth(1).len(), 1);
        assert_eq!(tracker.nodes_at_depth(2).len(), 1);
        assert_eq!(tracker.nodes_at_depth(3).len(), 0); // No nodes at depth 3
    }

    #[test]
    fn test_clear() {
        let mut tracker = HashTracker::new();
        let node_ref = NodeRef::new(test_page_id(1), 0);

        tracker.record(node_ref, None, 0, 0);
        assert_eq!(tracker.len(), 1);

        tracker.clear();
        assert!(tracker.is_empty());
        assert_eq!(tracker.max_depth(), 0);
    }
}
