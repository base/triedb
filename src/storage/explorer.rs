//! Explorer module for the interactive web UI.
//!
//! This module provides query methods specifically designed for the triedb explorer,
//! enabling interactive traversal of trie nodes and pages.

use crate::{
    context::TransactionContext,
    node::{Node, NodeKind},
    page::{Page, PageError, PageId, SlottedPage},
    pointer::Pointer,
    storage::{
        engine::{Error, StorageEngine},
        value::Value,
    },
};
use alloy_primitives::hex;
use alloy_trie::{nybbles, Nibbles};
use serde::Serialize;
use std::collections::HashSet;

/// Error type for explorer operations.
#[derive(Debug)]
pub enum ExplorerError {
    PageError(PageError),
    StorageError(Error),
    InvalidCellIndex(u8),
    NodeNotFound,
    InvalidSearchQuery(String),
}

impl From<PageError> for ExplorerError {
    fn from(e: PageError) -> Self {
        Self::PageError(e)
    }
}

impl From<Error> for ExplorerError {
    fn from(e: Error) -> Self {
        Self::StorageError(e)
    }
}

impl std::fmt::Display for ExplorerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExplorerError::PageError(e) => write!(f, "Page error: {:?}", e),
            ExplorerError::StorageError(e) => write!(f, "Storage error: {:?}", e),
            ExplorerError::InvalidCellIndex(i) => write!(f, "Invalid cell index: {}", i),
            ExplorerError::NodeNotFound => write!(f, "Node not found"),
            ExplorerError::InvalidSearchQuery(s) => write!(f, "Invalid search query: {}", s),
        }
    }
}

impl std::error::Error for ExplorerError {}

/// Represents a child pointer entry for branches.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ChildEntry {
    pub index: u8,
    pub pointer: ExplorerPointer,
}

/// Represents a pointer with location information for the UI.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ExplorerPointer {
    pub location_type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cell_index: Option<u8>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub page_id: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rlp_hash: Option<String>,
}

/// Represents a trie node with its location information for the UI.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ExplorerNode {
    pub page_id: u32,
    pub cell_index: u8,
    pub prefix: String,
    pub node_type: String,
    pub size_bytes: usize,

    // AccountLeaf fields
    #[serde(skip_serializing_if = "Option::is_none")]
    pub nonce: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub balance: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub storage_root: Option<ExplorerPointer>,

    // StorageLeaf fields
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value: Option<String>,

    // Branch fields
    #[serde(skip_serializing_if = "Option::is_none")]
    pub children: Option<Vec<ChildEntry>>,
}

/// Page information for the UI.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct PageInfo {
    pub page_id: u32,
    pub snapshot_id: u64,
    pub total_bytes: usize,
    pub used_bytes: usize,
    pub free_bytes: usize,
    pub cell_count: usize,
    pub occupancy_percent: f32,
}

/// Database metadata for the UI.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DatabaseInfo {
    pub snapshot_id: u64,
    pub root_node_hash: String,
    pub root_node_page_id: Option<u32>,
    pub total_page_count: u32,
    pub orphaned_pages: Vec<OrphanPageInfo>,
}

/// Orphan page information.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OrphanPageInfo {
    pub page_id: u32,
    pub orphaned_at_snapshot: u64,
}

/// Result of a path search.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct PathSearchResult {
    pub matched_path: String,
    pub node: ExplorerNode,
    pub path_to_node: Vec<ExplorerNode>,
}

/// Explorer service for querying trie data.
#[derive(Debug)]
pub struct ExplorerService<'a> {
    storage_engine: &'a StorageEngine,
}

impl<'a> ExplorerService<'a> {
    /// Creates a new ExplorerService.
    pub fn new(storage_engine: &'a StorageEngine) -> Self {
        Self { storage_engine }
    }

    /// Gets a node at a specific page and cell index.
    pub fn get_node_at(
        &self,
        context: &TransactionContext,
        page_id: PageId,
        cell_index: u8,
    ) -> Result<ExplorerNode, ExplorerError> {
        let slotted_page = self.storage_engine.get_slotted_page(context, page_id)?;
        let node: Node = slotted_page
            .get_value(cell_index)
            .map_err(|_| ExplorerError::InvalidCellIndex(cell_index))?;
        Ok(self.convert_node(page_id, cell_index, &node))
    }

    /// Gets all nodes on a page (including detecting orphaned cells).
    pub fn get_page_nodes(
        &self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<Vec<ExplorerNode>, ExplorerError> {
        let slotted_page = self.storage_engine.get_slotted_page(context, page_id)?;
        let num_cells = slotted_page.num_occupied_cells();
        let mut nodes = Vec::new();
        let mut found = 0;

        // Iterate through all cell indices, skipping deleted cells
        for cell_idx in 0..255u8 {
            if found >= num_cells {
                break;
            }
            match slotted_page.get_value::<Node>(cell_idx) {
                Ok(node) => {
                    nodes.push(self.convert_node(page_id, cell_idx, &node));
                    found += 1;
                }
                Err(_) => {
                    // Deleted cell or invalid - continue to next
                    continue;
                }
            }
        }
        Ok(nodes)
    }

    /// Gets page metadata.
    pub fn get_page_info(
        &self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<PageInfo, ExplorerError> {
        let page = self.get_page(context, page_id)?;
        let snapshot_id = page.snapshot_id();
        let slotted_page = SlottedPage::try_from(page)?;

        let used_bytes = slotted_page.num_occupied_bytes();
        let free_bytes = slotted_page.num_free_bytes();
        let total_bytes = Page::DATA_SIZE;
        let cell_count = slotted_page.num_occupied_cells();

        Ok(PageInfo {
            page_id: page_id.as_u32(),
            snapshot_id,
            total_bytes,
            used_bytes,
            free_bytes,
            cell_count,
            occupancy_percent: (used_bytes as f32 / total_bytes as f32) * 100.0,
        })
    }

    /// Walks all page-local descendants recursively from a starting cell.
    pub fn walk_page_local_descendants(
        &self,
        context: &TransactionContext,
        page_id: PageId,
        start_cell_index: u8,
    ) -> Result<Vec<ExplorerNode>, ExplorerError> {
        let slotted_page = self.storage_engine.get_slotted_page(context, page_id)?;
        let mut result = Vec::new();
        let mut stack = vec![start_cell_index];
        let mut visited = HashSet::new();

        while let Some(cell_idx) = stack.pop() {
            if visited.contains(&cell_idx) {
                continue;
            }
            visited.insert(cell_idx);

            let node: Node = match slotted_page.get_value(cell_idx) {
                Ok(n) => n,
                Err(_) => continue,
            };
            result.push(self.convert_node(page_id, cell_idx, &node));

            // Add same-page children to stack
            match node.kind() {
                NodeKind::Branch { children } => {
                    for child in children.iter().flatten() {
                        if let Some(child_cell_idx) = child.location().cell_index() {
                            stack.push(child_cell_idx);
                        }
                    }
                }
                NodeKind::AccountLeaf { storage_root, .. } => {
                    if let Some(ptr) = storage_root {
                        if let Some(child_cell_idx) = ptr.location().cell_index() {
                            stack.push(child_cell_idx);
                        }
                    }
                }
                NodeKind::StorageLeaf { .. } => {}
            }
        }
        Ok(result)
    }

    /// Searches by path and returns the matched node along with ancestors.
    pub fn search_by_path(
        &self,
        context: &TransactionContext,
        path: &Nibbles,
    ) -> Result<Option<PathSearchResult>, ExplorerError> {
        let root_page_id = match context.root_node_page_id {
            Some(id) => id,
            None => return Ok(None),
        };

        let mut path_to_node = Vec::new();
        let mut current_page_id = root_page_id;
        let mut current_cell_idx = 0u8;
        let mut path_offset = 0usize;

        loop {
            let slotted_page = self.storage_engine.get_slotted_page(context, current_page_id)?;
            let node: Node = slotted_page
                .get_value(current_cell_idx)
                .map_err(|_| ExplorerError::NodeNotFound)?;

            let explorer_node = self.convert_node(current_page_id, current_cell_idx, &node);
            path_to_node.push(explorer_node.clone());

            let prefix = node.prefix();
            let remaining_path = &path[path_offset..];
            let common_len = nybbles::common_prefix_length(remaining_path, prefix);

            if common_len < prefix.len() {
                // Path diverges - no match
                return Ok(None);
            }

            path_offset += common_len;

            if path_offset >= path.len() {
                // Found the node
                return Ok(Some(PathSearchResult {
                    matched_path: hex::encode(path.pack()),
                    node: explorer_node,
                    path_to_node,
                }));
            }

            // Navigate to child
            let next_nibble = path[path_offset];
            path_offset += 1;

            match node.kind() {
                NodeKind::Branch { children } => match &children[next_nibble as usize] {
                    Some(ptr) => {
                        if let Some(cell_idx) = ptr.location().cell_index() {
                            current_cell_idx = cell_idx;
                        } else if let Some(page_id) = ptr.location().page_id() {
                            current_page_id = page_id;
                            current_cell_idx = 0;
                        } else {
                            return Ok(None);
                        }
                    }
                    None => return Ok(None),
                },
                NodeKind::AccountLeaf { storage_root, .. } => {
                    // AccountLeaf doesn't consume a nibble for child navigation to storage
                    path_offset -= 1;
                    match storage_root {
                        Some(ptr) => {
                            if let Some(cell_idx) = ptr.location().cell_index() {
                                current_cell_idx = cell_idx;
                            } else if let Some(page_id) = ptr.location().page_id() {
                                current_page_id = page_id;
                                current_cell_idx = 0;
                            } else {
                                return Ok(None);
                            }
                        }
                        None => return Ok(None),
                    }
                }
                NodeKind::StorageLeaf { .. } => return Ok(None),
            }
        }
    }

    /// Gets database metadata including orphaned pages.
    pub fn get_database_info(&self) -> DatabaseInfo {
        let mut meta_manager = self.storage_engine.meta_manager.lock();

        // Collect orphaned pages first
        let orphaned_pages: Vec<OrphanPageInfo> = meta_manager
            .orphan_pages()
            .iter()
            .map(|op| OrphanPageInfo {
                page_id: op.page_id().as_u32(),
                orphaned_at_snapshot: op.orphaned_at(),
            })
            .collect();

        let active_slot = meta_manager.active_slot();
        DatabaseInfo {
            snapshot_id: active_slot.snapshot_id(),
            root_node_hash: hex::encode(active_slot.root_node_hash()),
            root_node_page_id: active_slot.root_node_page_id().map(|id| id.as_u32()),
            total_page_count: active_slot.page_count(),
            orphaned_pages,
        }
    }

    /// Gets the root page ID from metadata.
    pub fn get_root_page_id(&self) -> Option<PageId> {
        let meta_manager = self.storage_engine.meta_manager.lock();
        meta_manager.active_slot().root_node_page_id()
    }

    /// Helper to get a page from the page manager.
    fn get_page(
        &self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<Page<'_>, ExplorerError> {
        self.storage_engine
            .page_manager
            .get(context.snapshot_id, page_id)
            .map_err(|e| ExplorerError::PageError(e))
    }

    /// Converts a Node to ExplorerNode.
    fn convert_node(&self, page_id: PageId, cell_index: u8, node: &Node) -> ExplorerNode {
        // Convert nibbles to hex string directly (avoiding pack() which adds trailing 0 for odd lengths)
        let prefix: String = node.prefix().iter().map(|n| format!("{:X}", n)).collect();
        let size_bytes = node.size();

        match node.kind() {
            NodeKind::AccountLeaf { nonce_rlp, balance_rlp, code_hash, storage_root } => {
                let nonce: u64 = alloy_rlp::decode_exact(nonce_rlp).unwrap_or(0);
                let balance: alloy_primitives::U256 =
                    alloy_rlp::decode_exact(balance_rlp).unwrap_or_default();

                ExplorerNode {
                    page_id: page_id.as_u32(),
                    cell_index,
                    prefix,
                    node_type: "AccountLeaf".to_string(),
                    size_bytes,
                    nonce: Some(nonce),
                    balance: Some(format!("{}", balance)),
                    code_hash: Some(hex::encode(code_hash)),
                    storage_root: storage_root.as_ref().map(|p| self.convert_pointer(p)),
                    value: None,
                    children: None,
                }
            }
            NodeKind::StorageLeaf { value_rlp } => {
                let value: alloy_primitives::U256 =
                    alloy_rlp::decode_exact(value_rlp).unwrap_or_default();

                ExplorerNode {
                    page_id: page_id.as_u32(),
                    cell_index,
                    prefix,
                    node_type: "StorageLeaf".to_string(),
                    size_bytes,
                    nonce: None,
                    balance: None,
                    code_hash: None,
                    storage_root: None,
                    value: Some(format!("0x{:064x}", value)),
                    children: None,
                }
            }
            NodeKind::Branch { children } => {
                let child_entries: Vec<ChildEntry> = children
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, opt)| {
                        opt.as_ref().map(|p| ChildEntry {
                            index: idx as u8,
                            pointer: self.convert_pointer(p),
                        })
                    })
                    .collect();

                ExplorerNode {
                    page_id: page_id.as_u32(),
                    cell_index,
                    prefix,
                    node_type: "Branch".to_string(),
                    size_bytes,
                    nonce: None,
                    balance: None,
                    code_hash: None,
                    storage_root: None,
                    value: None,
                    children: Some(child_entries),
                }
            }
        }
    }

    /// Converts a Pointer to ExplorerPointer.
    fn convert_pointer(&self, pointer: &Pointer) -> ExplorerPointer {
        let location = pointer.location();
        let rlp_hash = pointer.rlp().as_hash().map(|h| hex::encode(h));

        if let Some(cell_idx) = location.cell_index() {
            ExplorerPointer {
                location_type: "SamePage".to_string(),
                cell_index: Some(cell_idx),
                page_id: None,
                rlp_hash,
            }
        } else if let Some(page_id) = location.page_id() {
            ExplorerPointer {
                location_type: "OtherPage".to_string(),
                cell_index: None,
                page_id: Some(page_id.as_u32()),
                rlp_hash,
            }
        } else {
            ExplorerPointer {
                location_type: "Unknown".to_string(),
                cell_index: None,
                page_id: None,
                rlp_hash,
            }
        }
    }
}
