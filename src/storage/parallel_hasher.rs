//! Level-based parallel hash computation for unhashed trie nodes.
//!
//! After an unhashed write operation populates a [`HashTracker`], this module computes
//! all pending hashes in parallel using level-based processing: depth 0 (leaves) first,
//! then depth 1, etc., up to the root. This naturally enforces hash dependency order.

use crate::{
    context::TransactionContext,
    node::Node,
    page::{PageId, SlottedPage, SlottedPageMut},
    pointer::Pointer,
    snapshot::SnapshotId,
    storage::{
        engine::{Error, StorageEngine},
        hash_tracker::{HashTracker, NodeRef, UnhashedNode},
    },
};
use std::fmt;
use alloy_primitives::B256;
use alloy_trie::{nodes::RlpNode, EMPTY_ROOT_HASH};
use fxhash::FxHashMap;
use rayon::prelude::*;

/// Result of computing a single node's hash.
#[derive(Debug, Clone)]
struct HashResult {
    /// The node that was hashed.
    #[allow(dead_code)]
    node_ref: NodeRef,
    /// The computed RLP node (contains hash or inline value).
    rlp: RlpNode,
    /// Parent node to update (None for root).
    parent: Option<NodeRef>,
    /// Child index in parent (0-15 for branch, 0 for account storage root).
    parent_child_index: u8,
}

/// Parallel hasher for computing trie node hashes after unhashed writes.
///
/// Uses level-based parallelism: processes all nodes at depth 0 (leaves) first,
/// then depth 1, etc. This ensures all children are hashed before their parents.
pub struct ParallelHasher<'a> {
    engine: &'a StorageEngine,
    tracker: &'a HashTracker,
}

impl fmt::Debug for ParallelHasher<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ParallelHasher")
            .field("tracker_nodes", &self.tracker.len())
            .field("tracker_max_depth", &self.tracker.max_depth())
            .finish_non_exhaustive()
    }
}

impl<'a> ParallelHasher<'a> {
    /// Creates a new [`ParallelHasher`].
    pub fn new(engine: &'a StorageEngine, tracker: &'a HashTracker) -> Self {
        Self { engine, tracker }
    }

    /// Computes all hashes bottom-up using level-based parallelism.
    ///
    /// Processes depth 0 (leaves) first, then depth 1, etc. up to root.
    /// Returns the new root hash after all computations.
    pub fn hash_all(&self, context: &mut TransactionContext) -> Result<B256, Error> {
        if self.tracker.is_empty() {
            return Ok(context.root_node_hash);
        }

        // Process each level from leaves (depth 0) to root (max_depth)
        for depth in 0..=self.tracker.max_depth() {
            self.hash_level(context, depth)?;
        }

        Ok(context.root_node_hash)
    }

    /// Hashes all nodes at a given depth in parallel.
    fn hash_level(&self, context: &mut TransactionContext, depth: u16) -> Result<(), Error> {
        let nodes = self.tracker.nodes_at_depth(depth);
        if nodes.is_empty() {
            return Ok(());
        }

        // Group nodes by page for cache efficiency
        let by_page = Self::group_by_page(nodes);

        // Extract snapshot_id for use in parallel context (SnapshotId is Copy + Send + Sync)
        let snapshot_id = context.snapshot_id;

        // Compute hashes in parallel
        // Each page group can be processed independently since nodes on different pages
        // don't share memory. Nodes on the same page are processed together to benefit
        // from reading the page once.
        let results: Vec<HashResult> = by_page
            .par_iter()
            .flat_map(|(page_id, page_nodes)| {
                self.hash_page_nodes(snapshot_id, *page_id, page_nodes)
            })
            .collect();

        // Apply parent pointer updates sequentially
        // This is necessary because:
        // 1. Multiple children may share the same parent
        // 2. Page mutations require &mut context
        self.apply_results(context, &results)?;

        Ok(())
    }

    /// Groups nodes by their page ID for efficient batch processing.
    fn group_by_page(nodes: &[UnhashedNode]) -> FxHashMap<PageId, Vec<&UnhashedNode>> {
        let mut by_page: FxHashMap<PageId, Vec<&UnhashedNode>> = FxHashMap::default();
        for node in nodes {
            by_page.entry(node.node_ref.page_id).or_default().push(node);
        }
        by_page
    }

    /// Computes hashes for all nodes on a single page.
    ///
    /// Reads the page once, then computes RLP for each node.
    fn hash_page_nodes(
        &self,
        snapshot_id: SnapshotId,
        page_id: PageId,
        nodes: &[&UnhashedNode],
    ) -> Vec<HashResult> {
        // Read page once for all nodes using snapshot_id directly
        let page = match self.engine.page_manager.get(snapshot_id, page_id) {
            Ok(p) => p,
            Err(_) => return Vec::new(),
        };

        let slotted = match SlottedPage::try_from(page) {
            Ok(s) => s,
            Err(_) => return Vec::new(),
        };

        nodes
            .iter()
            .filter_map(|node_info| {
                let node: Node = match slotted.get_value(node_info.node_ref.cell_index) {
                    Ok(n) => n,
                    Err(e) => {
                        eprintln!("Warning: failed to get node at cell {} on page {:?}: {:?}",
                            node_info.node_ref.cell_index, page_id, e);
                        return None;
                    }
                };
                let rlp = node.to_rlp_node();

                Some(HashResult {
                    node_ref: node_info.node_ref,
                    rlp,
                    parent: node_info.parent,
                    parent_child_index: node_info.parent_child_index,
                })
            })
            .collect()
    }

    /// Applies hash results by updating parent pointers.
    ///
    /// Groups updates by parent page to minimize page accesses.
    fn apply_results(
        &self,
        context: &mut TransactionContext,
        results: &[HashResult],
    ) -> Result<(), Error> {
        // Group updates by parent page
        // Key: parent's page_id
        // Value: Vec of (parent_cell_index, child_index, new_rlp)
        let mut parent_updates: FxHashMap<PageId, Vec<(u8, u8, RlpNode)>> = FxHashMap::default();

        for result in results {
            if let Some(parent_ref) = result.parent {
                parent_updates.entry(parent_ref.page_id).or_default().push((
                    parent_ref.cell_index,
                    result.parent_child_index,
                    result.rlp.clone(),
                ));
            } else {
                // This is the root node - update root hash
                context.root_node_hash = result.rlp.as_hash().unwrap_or(EMPTY_ROOT_HASH);
            }
        }

        // Apply updates page by page
        for (page_id, updates) in parent_updates {
            self.apply_page_updates(context, page_id, &updates)?;
        }

        Ok(())
    }

    /// Applies all pointer updates for nodes on a single page.
    fn apply_page_updates(
        &self,
        context: &mut TransactionContext,
        page_id: PageId,
        updates: &[(u8, u8, RlpNode)],
    ) -> Result<(), Error> {
        // Get mutable page - use clone-on-write semantics via engine's method
        let page = self.engine.get_mut_clone_for_hasher(context, page_id)?;
        let mut slotted = SlottedPageMut::try_from(page)?;

        for (parent_cell_idx, child_idx, rlp) in updates {
            let mut node: Node = slotted.get_value(*parent_cell_idx)?;

            // Get the old pointer to preserve location
            let old_pointer = match node.kind() {
                crate::node::NodeKind::Branch { children } => {
                    children[*child_idx as usize].as_ref()
                }
                crate::node::NodeKind::AccountLeaf { storage_root, .. } => storage_root.as_ref(),
                _ => None,
            };

            if let Some(old_ptr) = old_pointer {
                // Create new pointer with same location but computed hash
                let new_ptr = Pointer::new(old_ptr.location(), rlp.clone());
                node.set_child(*child_idx, new_ptr)?;
                slotted.set_value(*parent_cell_idx, &node)?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::hash_tracker::NodeRef;

    fn test_page_id(n: u32) -> PageId {
        PageId::new(n).unwrap()
    }

    #[test]
    fn test_group_by_page_empty() {
        let nodes: &[UnhashedNode] = &[];
        let by_page = ParallelHasher::group_by_page(nodes);
        assert!(by_page.is_empty());
    }

    #[test]
    fn test_group_by_page_single() {
        let nodes = vec![UnhashedNode {
            node_ref: NodeRef::new(test_page_id(1), 0),
            parent: None,
            parent_child_index: 0,
        }];

        let by_page = ParallelHasher::group_by_page(&nodes);
        assert_eq!(by_page.len(), 1);
        assert_eq!(by_page.get(&test_page_id(1)).unwrap().len(), 1);
    }

    #[test]
    fn test_group_by_page_multiple_same_page() {
        let nodes = vec![
            UnhashedNode {
                node_ref: NodeRef::new(test_page_id(1), 0),
                parent: None,
                parent_child_index: 0,
            },
            UnhashedNode {
                node_ref: NodeRef::new(test_page_id(1), 1),
                parent: None,
                parent_child_index: 0,
            },
            UnhashedNode {
                node_ref: NodeRef::new(test_page_id(1), 2),
                parent: None,
                parent_child_index: 0,
            },
        ];

        let by_page = ParallelHasher::group_by_page(&nodes);
        assert_eq!(by_page.len(), 1);
        assert_eq!(by_page.get(&test_page_id(1)).unwrap().len(), 3);
    }

    #[test]
    fn test_group_by_page_multiple_pages() {
        let nodes = vec![
            UnhashedNode {
                node_ref: NodeRef::new(test_page_id(1), 0),
                parent: None,
                parent_child_index: 0,
            },
            UnhashedNode {
                node_ref: NodeRef::new(test_page_id(2), 0),
                parent: None,
                parent_child_index: 0,
            },
            UnhashedNode {
                node_ref: NodeRef::new(test_page_id(1), 1),
                parent: None,
                parent_child_index: 0,
            },
            UnhashedNode {
                node_ref: NodeRef::new(test_page_id(3), 0),
                parent: None,
                parent_child_index: 0,
            },
        ];

        let by_page = ParallelHasher::group_by_page(&nodes);
        assert_eq!(by_page.len(), 3);
        assert_eq!(by_page.get(&test_page_id(1)).unwrap().len(), 2);
        assert_eq!(by_page.get(&test_page_id(2)).unwrap().len(), 1);
        assert_eq!(by_page.get(&test_page_id(3)).unwrap().len(), 1);
    }
}
