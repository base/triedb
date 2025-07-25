use crate::{
    context::TransactionContext,
    node::{Node, NodeKind, TrieValue},
    overlay::OverlayState,
    page::{PageId, SlottedPage},
    storage::engine::{Error, StorageEngine},
};
use alloy_primitives::B256;
use alloy_rlp::encode;
use alloy_trie::{HashBuilder, Nibbles, TrieAccount};

impl StorageEngine {
    /// Computes the root hash with overlay changes without persisting them.
    /// This uses alloy-trie's HashBuilder for efficient merkle root computation.
    pub fn compute_root_with_overlay(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
    ) -> Result<B256, Error> {
        if overlay.is_empty() {
            // No overlay changes, return current root
            return Ok(context.root_node_hash);
        }

        let mut hash_builder = HashBuilder::default();

        // Use proper trie traversal with overlay integration
        self.traverse_with_overlay(context, overlay, &mut hash_builder)?;

        let root = hash_builder.root();
        Ok(root)
    }

    /// Helper method to traverse the existing trie and integrate with overlay
    fn traverse_with_overlay(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
        hash_builder: &mut HashBuilder,
    ) -> Result<(), Error> {
        // First, collect all existing values from disk
        if let Some(root_page_id) = context.root_node_page_id {
            self.traverse_page_with_overlay(
                context,
                overlay,
                hash_builder,
                root_page_id,
                &Nibbles::new(),
                Some(context.root_node_hash),
            )?;
        } else {
            // No root page, just add all overlay changes to the hash builder
            for (path, value) in overlay.iter() {
                if let Some(trie_value) = value {
                    let rlp_encoded = self.encode_trie_value(trie_value)?;
                    hash_builder.add_leaf(path, &rlp_encoded);
                }
            }
        }

        Ok(())
    }

    /// Traverse a specific page with overlay integration
    fn traverse_page_with_overlay(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
        hash_builder: &mut HashBuilder,
        page_id: PageId,
        path_prefix: &Nibbles,
        node_hash: Option<B256>,
    ) -> Result<(), Error> {
        let page = self.get_page(context, page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;

        // Start at the root cell (cell_index = 0) and recurse properly
        self.traverse_node_with_overlay(
            context,
            overlay,
            hash_builder,
            &slotted_page,
            0, // Start from root cell
            path_prefix,
            node_hash,
        )
    }

    /// Traverse a specific node with overlay integration
    fn traverse_node_with_overlay(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
        hash_builder: &mut HashBuilder,
        slotted_page: &SlottedPage,
        cell_index: u8,
        path_prefix: &Nibbles,
        node_hash: Option<B256>,
    ) -> Result<(), Error> {
        let node: Node = slotted_page.get_value(cell_index)?;
        let full_path = {
            let mut full = path_prefix.clone();
            full.extend_from_slice_unchecked(node.prefix());
            full
        };

        let pre_overlay = overlay.sub_slice_before_prefix(&full_path);
        let post_overlay = overlay.sub_slice_after_prefix(&full_path);

        // Add all pre-overlay changes
        for (path, value) in pre_overlay.iter() {
            if let Some(trie_value) = value {
                let rlp_encoded = self.encode_trie_value(trie_value)?;
                hash_builder.add_leaf(path, &rlp_encoded);
            }
        }

        // Check if this node is affected by overlay
        if overlay.affects_path(&full_path) {
            // This node or its descendants are affected by overlay
            self.handle_affected_node_with_overlay(
                context,
                overlay,
                hash_builder,
                slotted_page,
                &node,
                &full_path,
            )?;
        } else {
            // Node not affected by overlay, use disk value as-is
            self.handle_unaffected_node(
                context,
                hash_builder,
                slotted_page,
                &node,
                &full_path,
                node_hash,
            )?;
        }

        for (path, value) in post_overlay.iter() {
            if let Some(trie_value) = value {
                let rlp_encoded = self.encode_trie_value(trie_value)?;
                hash_builder.add_leaf(path, &rlp_encoded);
            }
        }

        Ok(())
    }

    /// Handle a node that is affected by overlay changes
    fn handle_affected_node_with_overlay(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
        hash_builder: &mut HashBuilder,
        slotted_page: &SlottedPage,
        node: &Node,
        full_path: &Nibbles,
    ) -> Result<(), Error> {
        use crate::node::NodeKind;

        match node.kind() {
            NodeKind::AccountLeaf { .. } if full_path.len() == 64 => {
                // Account leaf at address level - handle potential storage overlays
                self.handle_account_leaf_with_overlay(
                    context,
                    overlay,
                    hash_builder,
                    slotted_page,
                    node,
                    full_path,
                )?;
            }
            NodeKind::StorageLeaf { .. } => {
                // Storage leaf - handle with simple leaf logic
                // This can be either 128-nibble paths (account-level traversal) or 64-nibble paths
                // (storage-level traversal)
                if let Some(overlay_value) = overlay.lookup(full_path) {
                    // Use overlay value
                    if let Some(trie_value) = overlay_value {
                        let rlp_encoded = self.encode_trie_value(trie_value)?;
                        hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
                    }
                    // If overlay_value is None, it's a deletion - skip
                } else {
                    // No exact overlay match, use disk value
                    let node_value = node.value()?;
                    let rlp_encoded = self.encode_trie_value(&node_value)?;
                    hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
                }
            }
            NodeKind::Branch { .. } => {
                // Branch node - recurse into each child with overlay sub-slicing
                self.traverse_branch_node_with_overlay(
                    context,
                    overlay,
                    hash_builder,
                    slotted_page,
                    node,
                    full_path,
                )?;
            }
            _ => {
                // Other leaf nodes - handle with simple leaf logic
                if let Some(overlay_value) = overlay.lookup(full_path) {
                    if let Some(trie_value) = overlay_value {
                        let rlp_encoded = self.encode_trie_value(trie_value)?;
                        hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
                    }
                } else {
                    let node_value = node.value()?;
                    let rlp_encoded = self.encode_trie_value(&node_value)?;
                    hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
                }
            }
        }
        Ok(())
    }

    /// Handle a node that is not affected by overlay changes
    fn handle_unaffected_node(
        &self,
        _context: &TransactionContext,
        hash_builder: &mut HashBuilder,
        _slotted_page: &SlottedPage,
        node: &Node,
        full_path: &Nibbles,
        node_hash: Option<B256>,
    ) -> Result<(), Error> {
        match node.kind() {
            NodeKind::AccountLeaf { .. } | NodeKind::StorageLeaf { .. } => {
                // Account leaf - use disk value directly
                let node_value = node.value()?;
                let rlp_encoded = self.encode_trie_value(&node_value)?;
                hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
            }
            NodeKind::Branch { .. } => {
                // Branch node - since it's unaffected by overlay, we can use its existing hash
                // This is much more efficient than recursing into all children
                if let Some(hash) = node_hash {
                    // Use the precomputed hash directly for this branch subtree
                    // stored_in_database = true since this is an existing node from disk
                    hash_builder.add_branch(full_path.clone(), hash, true);
                } else {
                    // Fallback: if we don't have the hash, we need to compute it
                    // This shouldn't normally happen but provides a safety net
                    let node_value = node.value()?;
                    let rlp_encoded = self.encode_trie_value(&node_value)?;
                    hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
                }
            }
        }
        Ok(())
    }

    /// Handle traversal of branch nodes with overlay integration
    fn traverse_branch_node_with_overlay(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
        hash_builder: &mut HashBuilder,
        slotted_page: &SlottedPage,
        node: &Node,
        full_path: &Nibbles,
    ) -> Result<(), Error> {
        // For each child in the branch node (0-15), check if there are relevant overlay changes
        // and recursively traverse child nodes
        for child_index in 0..16 {
            // Construct the path for this child
            let mut child_path = full_path.clone();
            child_path.push(child_index);

            // Create sub-slice of overlay for this child's subtree
            let child_overlay = overlay.sub_slice_for_prefix(&child_path);

            if let Ok(Some(child_pointer)) = node.child(child_index) {
                // Child exists on disk - traverse it with overlay integration
                let child_hash = child_pointer.rlp().as_hash();
                let child_location = child_pointer.location();

                if let Some(child_cell_index) = child_location.cell_index() {
                    // Child is in the same page
                    self.traverse_node_with_overlay(
                        context,
                        &child_overlay,
                        hash_builder,
                        slotted_page,
                        child_cell_index,
                        &child_path,
                        child_hash,
                    )?;
                } else if let Some(child_page_id) = child_location.page_id() {
                    // Child is in a different page - add safety check
                    if self.page_exists(context, child_page_id) {
                        self.traverse_page_with_overlay(
                            context,
                            &child_overlay,
                            hash_builder,
                            child_page_id,
                            &child_path,
                            child_hash,
                        )?;
                    }
                }
            } else {
                // No child exists on disk, but check if overlay has leaves for this subtree
                if !child_overlay.is_empty() {
                    // There are overlay changes that create new nodes in this subtree
                    // Add all overlay leaves for this child subtree
                    for (path, value) in child_overlay.iter() {
                        if let Some(trie_value) = value {
                            let rlp_encoded = self.encode_trie_value(trie_value)?;
                            hash_builder.add_leaf(path, &rlp_encoded);
                        }
                        // Tombstones (None values) are skipped
                    }
                }
            }
        }
        Ok(())
    }

    /// Handle an account leaf with potential storage overlays using iterative HashBuilder approach
    fn handle_account_leaf_with_overlay(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
        hash_builder: &mut HashBuilder,
        slotted_page: &SlottedPage,
        node: &Node,
        full_path: &Nibbles,
    ) -> Result<(), Error> {
        // Get the original account from the node
        let original_account = match node.value()? {
            TrieValue::Account(account) => account,
            _ => {
                // This shouldn't happen for AccountLeaf nodes, but handle gracefully
                let rlp_encoded = self.encode_trie_value(&node.value()?)?;
                hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
                return Ok(());
            }
        };

        // Check if this account is directly overlaid (account-level changes)
        if let Some(overlay_value) = overlay.lookup(full_path) {
            // Direct account overlay - use overlay value, but still check for storage overlays
            if let Some(trie_value) = overlay_value {
                // Even with account overlay, we might need to compute storage root for storage
                // overlays
                if let TrieValue::Account(overlay_account) = trie_value {
                    // Check if there are storage overlays for this account
                    let storage_overlays = overlay.find_prefix_range(full_path);
                    let has_storage_overlays = storage_overlays
                        .iter()
                        .any(|(path, _)| path.len() == 128 && path.len() > full_path.len());

                    if has_storage_overlays {
                        // Compute new storage root with overlays
                        let new_storage_root = self.compute_storage_root_iteratively(
                            context,
                            node, // Use the original node for storage traversal
                            full_path,
                            &storage_overlays,
                            slotted_page,
                        )?;

                        // Create modified account with new storage root
                        let mut modified_account = overlay_account.clone();
                        modified_account.storage_root = new_storage_root;
                        let rlp_encoded =
                            self.encode_trie_value(&TrieValue::Account(modified_account))?;
                        hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
                    } else {
                        // No storage overlays, use account overlay as-is
                        let rlp_encoded = self.encode_trie_value(trie_value)?;
                        hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
                    }
                } else {
                    // Not an account value, just use as-is
                    let rlp_encoded = self.encode_trie_value(trie_value)?;
                    hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
                }
            }
            // If overlay_value is None, it's a deletion - skip
            return Ok(());
        }

        // Check if there are any storage overlays for this account
        // Storage overlays have 128-nibble paths that start with this account's 64-nibble path
        let storage_overlays = overlay.find_prefix_range(full_path);
        let has_storage_overlays = storage_overlays
            .iter()
            .any(|(path, _)| path.len() == 128 && path.len() > full_path.len());

        if !has_storage_overlays {
            // No storage overlays for this account, use original account
            let rlp_encoded = self.encode_trie_value(&TrieValue::Account(original_account))?;
            hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
            return Ok(());
        }

        // We have storage overlays, need to compute a new storage root using iterative approach
        let new_storage_root = self.compute_storage_root_iteratively(
            context,
            node,
            full_path,
            &storage_overlays,
            slotted_page,
        )?;

        // Create a modified account with the new storage root
        let mut modified_account = original_account;
        modified_account.storage_root = new_storage_root;

        // Add the modified account to the main HashBuilder
        let rlp_encoded = self.encode_trie_value(&TrieValue::Account(modified_account))?;
        hash_builder.add_leaf(full_path.clone(), &rlp_encoded);

        Ok(())
    }

    /// Compute the storage root for an account using iterative HashBuilder approach with prefix
    /// offset
    fn compute_storage_root_iteratively(
        &self,
        context: &TransactionContext,
        account_node: &Node,
        _account_path: &Nibbles,
        storage_overlays: &OverlayState,
        slotted_page: &SlottedPage,
    ) -> Result<B256, Error> {
        // Create a storage-specific overlay with 64-nibble prefix offset
        // This converts 128-nibble storage paths to 64-nibble storage-relative paths
        let storage_overlay = storage_overlays.with_prefix_offset(64);

        let mut storage_hash_builder = HashBuilder::default();

        // Get the original account's storage root to determine if we need to traverse existing
        // storage
        let original_storage_root = match account_node.value()? {
            TrieValue::Account(account) => account.storage_root,
            _ => return Err(Error::NodeError(crate::node::NodeError::NoValue)), /* This shouldn't happen for account nodes */
        };

        // If the account has existing storage, traverse the existing storage trie
        if original_storage_root != alloy_trie::EMPTY_ROOT_HASH {
            // Try to find the storage root page from the account node's direct child
            if let Ok(Some(storage_root_pointer)) = account_node.direct_child() {
                let storage_root_location = storage_root_pointer.location();
                let storage_root_hash = storage_root_pointer.rlp().as_hash();

                if let Some(storage_page_id) = storage_root_location.page_id() {
                    // Traverse the existing storage trie with storage overlays
                    self.traverse_page_with_overlay(
                        context,
                        &storage_overlay,
                        &mut storage_hash_builder,
                        storage_page_id,
                        &Nibbles::new(), // Start with empty path for storage root
                        storage_root_hash,
                    )?;
                } else if let Some(storage_cell_index) = storage_root_location.cell_index() {
                    // Storage root is in the same page as the account
                    self.traverse_node_with_overlay(
                        context,
                        &storage_overlay,
                        &mut storage_hash_builder,
                        slotted_page,
                        storage_cell_index,
                        &Nibbles::new(), // Start with empty path for storage root
                        storage_root_hash,
                    )?;
                }
            }
        } else {
            // No existing storage, just add overlay changes
            for (path, value) in storage_overlay.iter() {
                if let Some(trie_value) = value {
                    let rlp_encoded = self.encode_trie_value(trie_value)?;
                    storage_hash_builder.add_leaf(path, &rlp_encoded);
                }
            }
        }

        let computed_root = storage_hash_builder.root();
        Ok(computed_root)
    }

    /// Check if a page exists in the storage
    fn page_exists(&self, context: &TransactionContext, page_id: PageId) -> bool {
        self.get_page(context, page_id).is_ok()
    }

    /// Helper to encode TrieValue as RLP
    fn encode_trie_value(&self, trie_value: &TrieValue) -> Result<Vec<u8>, Error> {
        let rlp_encoded = match trie_value {
            TrieValue::Account(account) => {
                let trie_account = TrieAccount {
                    nonce: account.nonce,
                    balance: account.balance,
                    storage_root: account.storage_root,
                    code_hash: account.code_hash,
                };
                encode(trie_account)
            }
            TrieValue::Storage(storage_value) => encode(storage_value),
        };
        Ok(rlp_encoded)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        account::Account, database::Database, node::TrieValue, overlay::OverlayStateMut,
        path::AddressPath,
    };
    use alloy_primitives::{address, U256};
    use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
    use tempdir::TempDir;

    #[test]
    fn test_empty_overlay_root() {
        let tmp_dir = TempDir::new("test_overlay_root_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let context = db.storage_engine.read_context();
        let empty_overlay = OverlayStateMut::new().freeze();

        let root = db.storage_engine.compute_root_with_overlay(&context, &empty_overlay).unwrap();
        assert_eq!(root, context.root_node_hash);
    }

    #[test]
    fn test_overlay_root_with_empty_db() {
        let tmp_dir = TempDir::new("test_overlay_root_changes_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let context = db.storage_engine.read_context();

        // Create overlay with some changes
        let mut overlay_mut = OverlayStateMut::new();
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let address_path = AddressPath::for_address(address);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        overlay_mut.insert(address_path.into(), Some(TrieValue::Account(account)));
        let overlay = overlay_mut.freeze();

        // Compute root with overlay
        let root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();

        // The root should be different from the empty root (since we have changes)
        assert_ne!(root, EMPTY_ROOT_HASH);
    }

    #[test]
    fn test_overlay_root_with_changes() {
        let tmp_dir = TempDir::new("test_overlay_root_changes_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // First, add an account using set_values (following the same pattern as other tests)
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let address_path = AddressPath::for_address(address);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        db.storage_engine
            .set_values(
                &mut context,
                &mut [(address_path.clone().into(), Some(TrieValue::Account(account)))],
            )
            .unwrap();

        let initial_root = context.root_node_hash;
        assert_ne!(initial_root, EMPTY_ROOT_HASH);

        // Test that we can compute root with empty overlay first (should match initial_root)
        let empty_overlay = OverlayStateMut::new().freeze();
        let root_with_empty_overlay =
            db.storage_engine.compute_root_with_overlay(&context, &empty_overlay).unwrap();
        assert_eq!(root_with_empty_overlay, initial_root);

        // Now test with actual overlay changes - modify the same account with different values
        let mut overlay_mut = OverlayStateMut::new();
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        overlay_mut.insert(address_path.clone().into(), Some(TrieValue::Account(account2.clone())));
        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify: commit the overlay changes and compare roots
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context,
                &mut [(address_path.into(), Some(TrieValue::Account(account2)))],
            )
            .unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(overlay_root, committed_root, "Overlay root should match committed root");
    }

    #[test]
    fn test_overlay_with_controlled_paths() {
        let tmp_dir = TempDir::new("test_overlay_controlled_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create specific address paths to control trie structure
        // These paths are designed to create branch nodes at specific positions

        // Path 1: starts with 0x0... (first nibble = 0)
        let path1 = AddressPath::new(Nibbles::from_nibbles([
            0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        ]));

        // Path 2: starts with 0x1... (first nibble = 1)
        let path2 = AddressPath::new(Nibbles::from_nibbles([
            0x1, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        ]));

        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // Add both accounts to disk - this should create a branch node at the root
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (path1.clone().into(), Some(TrieValue::Account(account1.clone()))),
                    (path2.clone().into(), Some(TrieValue::Account(account2.clone()))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;
        assert_ne!(initial_root, EMPTY_ROOT_HASH);

        // Test Case 1: Overlay that affects only path1 (child 0) - path2 subtree should use
        // add_branch optimization
        let account1_updated = Account::new(10, U256::from(1000), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut
            .insert(path1.clone().into(), Some(TrieValue::Account(account1_updated.clone())));
        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the change
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context,
                &mut [
                    (path1.clone().into(), Some(TrieValue::Account(account1_updated.clone()))),
                    (path2.clone().into(), Some(TrieValue::Account(account2.clone()))),
                ],
            )
            .unwrap();
        assert_eq!(
            overlay_root, verification_context.root_node_hash,
            "Case 1: Overlay root should match committed root"
        );

        // Test Case 2: Overlay that creates a new account in an empty subtree (None child case)
        // Path 3: starts with 0x2... (first nibble = 2) - this child doesn't exist on disk
        let path3 = AddressPath::new(Nibbles::from_nibbles([
            0x2, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        ]));

        let account3 = Account::new(3, U256::from(300), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let mut overlay_mut2 = OverlayStateMut::new();
        overlay_mut2.insert(path3.clone().into(), Some(TrieValue::Account(account3.clone())));
        let overlay2 = overlay_mut2.freeze();

        let overlay_root2 =
            db.storage_engine.compute_root_with_overlay(&context, &overlay2).unwrap();
        assert_ne!(overlay_root2, initial_root);
        assert_ne!(overlay_root2, overlay_root);

        // Verify by committing the change
        let mut verification_context2 = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context2,
                &mut [
                    (path1.clone().into(), Some(TrieValue::Account(account1.clone()))),
                    (path2.clone().into(), Some(TrieValue::Account(account2.clone()))),
                    (path3.clone().into(), Some(TrieValue::Account(account3.clone()))),
                ],
            )
            .unwrap();
        assert_eq!(
            overlay_root2, verification_context2.root_node_hash,
            "Case 2: Overlay root should match committed root"
        );

        // Test Case 3: Mixed overlay - affects one subtree, creates new subtree, leaves one
        // unaffected
        let mut overlay_mut3 = OverlayStateMut::new();
        overlay_mut3
            .insert(path1.clone().into(), Some(TrieValue::Account(account1_updated.clone()))); // Modify existing
        overlay_mut3.insert(path3.clone().into(), Some(TrieValue::Account(account3.clone()))); // Create new
                                                                                               // path2 is left unaffected - should use add_branch optimization
        let overlay3 = overlay_mut3.freeze();

        let overlay_root3 =
            db.storage_engine.compute_root_with_overlay(&context, &overlay3).unwrap();
        assert_ne!(overlay_root3, initial_root);
        assert_ne!(overlay_root3, overlay_root);
        assert_ne!(overlay_root3, overlay_root2);

        // Verify by committing the changes
        let mut verification_context3 = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context3,
                &mut [
                    (path1.clone().into(), Some(TrieValue::Account(account1_updated))),
                    (path2.clone().into(), Some(TrieValue::Account(account2))),
                    (path3.clone().into(), Some(TrieValue::Account(account3))),
                ],
            )
            .unwrap();
        assert_eq!(
            overlay_root3, verification_context3.root_node_hash,
            "Case 3: Overlay root should match committed root"
        );
    }

    #[test]
    fn test_overlay_tombstones() {
        let tmp_dir = TempDir::new("test_overlay_tombstones_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        // Step 1: Write account 1 and compute root
        let mut context1 = db.storage_engine.write_context();
        let path1 = AddressPath::new(Nibbles::from_nibbles([
            0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        ]));
        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        db.storage_engine
            .set_values(
                &mut context1,
                &mut [(path1.clone().into(), Some(TrieValue::Account(account1.clone())))],
            )
            .unwrap();
        let root_with_account1 = context1.root_node_hash;

        // Step 2: Add account 2
        let mut context2 = db.storage_engine.write_context();
        let path2 = AddressPath::new(Nibbles::from_nibbles([
            0x1, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        ]));
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        db.storage_engine
            .set_values(
                &mut context2,
                &mut [
                    (path1.clone().into(), Some(TrieValue::Account(account1.clone()))),
                    (path2.clone().into(), Some(TrieValue::Account(account2.clone()))),
                ],
            )
            .unwrap();
        let root_with_both_accounts = context2.root_node_hash;
        assert_ne!(root_with_both_accounts, root_with_account1);

        // Step 3: Overlay a tombstone for account 2 and compute root
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(path2.clone().into(), None); // Delete account2
        let overlay = overlay_mut.freeze();

        let overlay_root_with_deletion =
            db.storage_engine.compute_root_with_overlay(&context2, &overlay).unwrap();
        assert_ne!(overlay_root_with_deletion, root_with_both_accounts);

        // Step 4: Verify by actually erasing account 2 and computing root
        let mut context3 = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut context3,
                &mut [
                    (path1.clone().into(), Some(TrieValue::Account(account1))),
                    // path2 is omitted - effectively deleted
                ],
            )
            .unwrap();
        let root_after_deletion = context3.root_node_hash;

        // The overlay root with tombstone should match the root after actual deletion
        assert_eq!(
            overlay_root_with_deletion, root_after_deletion,
            "Tombstone overlay root should match actual deletion root"
        );

        // Both should equal the original root with just account1
        assert_eq!(
            overlay_root_with_deletion, root_with_account1,
            "After deleting account2, root should match original single-account root"
        );
        assert_eq!(
            root_after_deletion, root_with_account1,
            "After deleting account2, committed root should match original single-account root"
        );
    }

    #[test]
    fn test_overlay_with_storage_changes() {
        let tmp_dir = TempDir::new("test_overlay_storage_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create an account with some storage
        let account_address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account_path = AddressPath::for_address(account_address);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // Create storage paths for the account
        let storage_key1 = U256::from(42);
        let storage_key2 = U256::from(99);
        let storage_path1 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key1.into());
        let storage_path2 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key2.into());

        let storage_value1 = U256::from(123);
        let storage_value2 = U256::from(456);

        // Set up initial state with account and storage
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.full_path(), Some(TrieValue::Storage(storage_value1.into()))),
                    (storage_path2.full_path(), Some(TrieValue::Storage(storage_value2.into()))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;
        assert_ne!(initial_root, EMPTY_ROOT_HASH);

        // Test Case 1: Overlay that modifies existing storage
        let mut overlay_mut = OverlayStateMut::new();
        let new_storage_value1 = U256::from(999);
        overlay_mut
            .insert(storage_path1.full_path(), Some(TrieValue::Storage(new_storage_value1.into())));
        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the storage change
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context,
                &mut [
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (
                        storage_path1.full_path(),
                        Some(TrieValue::Storage(new_storage_value1.into())),
                    ),
                    (storage_path2.full_path(), Some(TrieValue::Storage(storage_value2.into()))),
                ],
            )
            .unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(
            overlay_root, committed_root,
            "Storage overlay root should match committed root"
        );

        // Test Case 2: Overlay that adds new storage
        let mut overlay_mut2 = OverlayStateMut::new();
        let storage_key3 = U256::from(200);
        let storage_path3 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key3.into());
        let storage_value3 = U256::from(789);
        overlay_mut2
            .insert(storage_path3.full_path(), Some(TrieValue::Storage(storage_value3.into())));
        let overlay2 = overlay_mut2.freeze();

        let overlay_root2 =
            db.storage_engine.compute_root_with_overlay(&context, &overlay2).unwrap();
        assert_ne!(overlay_root2, initial_root);
        assert_ne!(overlay_root2, overlay_root);

        // Verify by committing the new storage
        let mut verification_context2 = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context2,
                &mut [
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.full_path(), Some(TrieValue::Storage(storage_value1.into()))),
                    (storage_path2.full_path(), Some(TrieValue::Storage(storage_value2.into()))),
                    (storage_path3.full_path(), Some(TrieValue::Storage(storage_value3.into()))),
                ],
            )
            .unwrap();
        let committed_root2 = verification_context2.root_node_hash;

        assert_eq!(
            overlay_root2, committed_root2,
            "New storage overlay root should match committed root"
        );

        // Test Case 3: Overlay that deletes storage (tombstone)
        let mut overlay_mut3 = OverlayStateMut::new();
        overlay_mut3.insert(storage_path2.full_path(), None); // Delete storage slot
        let overlay3 = overlay_mut3.freeze();

        let overlay_root3 =
            db.storage_engine.compute_root_with_overlay(&context, &overlay3).unwrap();
        assert_ne!(overlay_root3, initial_root);

        // Verify by committing the deletion
        let mut verification_context3 = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context3,
                &mut [
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.full_path(), Some(TrieValue::Storage(storage_value1.into()))),
                    // storage_path2 is omitted - effectively deleted
                ],
            )
            .unwrap();
        let committed_root3 = verification_context3.root_node_hash;

        assert_eq!(
            overlay_root3, committed_root3,
            "Storage deletion overlay root should match committed root"
        );

        // Test Case 4: Combined account and storage changes
        let mut overlay_mut4 = OverlayStateMut::new();
        let updated_account = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        overlay_mut4
            .insert(account_path.clone().into(), Some(TrieValue::Account(updated_account.clone())));
        overlay_mut4
            .insert(storage_path1.full_path(), Some(TrieValue::Storage(new_storage_value1.into())));
        let overlay4 = overlay_mut4.freeze();

        let overlay_root4 =
            db.storage_engine.compute_root_with_overlay(&context, &overlay4).unwrap();
        assert_ne!(overlay_root4, initial_root);

        // Note: For combined account+storage changes, the account overlay takes precedence
        // and storage overlays should still be applied to compute the new storage root
        // This is a complex case that exercises our account overlay + storage overlay logic
    }

    #[test]
    fn test_overlay_performance_cases() {
        let tmp_dir = TempDir::new("test_overlay_performance_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create a larger trie with multiple levels to test add_branch optimization
        let accounts_data = [
            ([0x0, 0x0], Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY)),
            ([0x0, 0x1], Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY)),
            ([0x1, 0x0], Account::new(3, U256::from(300), EMPTY_ROOT_HASH, KECCAK_EMPTY)),
            ([0x1, 0x1], Account::new(4, U256::from(400), EMPTY_ROOT_HASH, KECCAK_EMPTY)),
            ([0x2, 0x0], Account::new(5, U256::from(500), EMPTY_ROOT_HASH, KECCAK_EMPTY)),
        ];

        let mut changes = Vec::new();
        for (prefix, account) in accounts_data.iter() {
            let mut nibbles = vec![prefix[0], prefix[1]];
            // Pad to 64 nibbles for address path
            nibbles.extend(vec![0x0; 62]);
            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
            changes.push((path.into(), Some(TrieValue::Account(account.clone()))));
        }

        db.storage_engine.set_values(&mut context, &mut changes).unwrap();
        let initial_root = context.root_node_hash;

        // Test: Modify only one leaf in a large subtree
        // This should trigger add_branch optimization for unaffected subtrees
        let mut nibbles = vec![0x0, 0x0];
        nibbles.extend(vec![0x0; 62]);
        let modify_path = AddressPath::new(Nibbles::from_nibbles(nibbles));

        let updated_account = Account::new(10, U256::from(1000), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut
            .insert(modify_path.clone().into(), Some(TrieValue::Account(updated_account.clone())));
        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify the computation is correct by comparing with direct modification
        let mut verification_context = db.storage_engine.write_context();
        let mut verification_changes = Vec::new();
        for (i, (prefix, account)) in accounts_data.iter().enumerate() {
            let mut nibbles = vec![prefix[0], prefix[1]];
            nibbles.extend(vec![0x0; 62]);
            let path = AddressPath::new(Nibbles::from_nibbles(nibbles));

            if i == 0 {
                // Use updated account for first entry
                verification_changes
                    .push((path.into(), Some(TrieValue::Account(updated_account.clone()))));
            } else {
                verification_changes.push((path.into(), Some(TrieValue::Account(account.clone()))));
            }
        }

        db.storage_engine.set_values(&mut verification_context, &mut verification_changes).unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(
            overlay_root, committed_root,
            "Performance test: Overlay root should match committed root"
        );
    }

    #[test]
    fn test_debug_adding_storage_slot_overlay() {
        let tmp_dir = TempDir::new("test_add_storage_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create account with 1 storage slot
        let account_address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(account_address);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let storage_key1 = U256::from(10);
        let storage_path1 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key1.into());

        // Set up initial state with 1 storage slot
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(111).into()))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Add a NEW storage slot via overlay
        let mut overlay_mut = OverlayStateMut::new();
        let storage_key2 = U256::from(20); // New storage key
        let storage_path2 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key2.into());
        overlay_mut
            .insert(storage_path2.full_path(), Some(TrieValue::Storage(U256::from(222).into())));
        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the addition
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine.set_values(&mut verification_context, &mut [
            (account_path.into(), Some(TrieValue::Account(account))),
            (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(111).into()))), // Original
            (storage_path2.full_path(), Some(TrieValue::Storage(U256::from(222).into()))), // New
        ]).unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(overlay_root, committed_root, "Adding storage slot via overlay should match");
    }

    #[test]
    fn test_debug_minimal_multi_account_overlay() {
        let tmp_dir = TempDir::new("test_minimal_multi_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create just 2 accounts with 1 storage slot each
        let account1_address = address!("0x0000000000000000000000000000000000000001");
        let account2_address = address!("0x0000000000000000000000000000000000000002");

        let account1_path = AddressPath::for_address(account1_address);
        let account2_path = AddressPath::for_address(account2_address);

        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // One storage slot for each account
        let storage1_key = U256::from(10);
        let storage2_key = U256::from(20);
        let storage1_path =
            crate::path::StoragePath::for_address_and_slot(account1_address, storage1_key.into());
        let storage2_path =
            crate::path::StoragePath::for_address_and_slot(account2_address, storage2_key.into());

        // Set up initial state
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account1_path.clone().into(), Some(TrieValue::Account(account1.clone()))),
                    (account2_path.clone().into(), Some(TrieValue::Account(account2.clone()))),
                    (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(111).into()))),
                    (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(222).into()))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Modify just one storage value per account via overlay
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut
            .insert(storage1_path.full_path(), Some(TrieValue::Storage(U256::from(999).into())));
        overlay_mut
            .insert(storage2_path.full_path(), Some(TrieValue::Storage(U256::from(888).into())));
        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the changes
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context,
                &mut [
                    (account1_path.into(), Some(TrieValue::Account(account1))),
                    (account2_path.into(), Some(TrieValue::Account(account2))),
                    (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(999).into()))),
                    (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(888).into()))),
                ],
            )
            .unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(
            overlay_root, committed_root,
            "Minimal multi-account storage overlay should match"
        );
    }

    #[test]
    fn test_debug_multiple_storage_overlays_same_account() {
        let tmp_dir = TempDir::new("test_debug_multiple_overlays_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create one account with 2 initial storage slots
        let account_address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account_path = AddressPath::for_address(account_address);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let storage_key1 = U256::from(10);
        let storage_key2 = U256::from(20);
        let storage_path1 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key1.into());
        let storage_path2 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key2.into());

        // Set up initial state
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(111).into()))),
                    (storage_path2.full_path(), Some(TrieValue::Storage(U256::from(222).into()))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Apply MULTIPLE storage overlays to the same account
        let mut overlay_mut = OverlayStateMut::new();

        // Modify existing storage slot 1
        overlay_mut
            .insert(storage_path1.full_path(), Some(TrieValue::Storage(U256::from(1111).into())));

        // Add new storage slot 3
        let storage_key3 = U256::from(40);
        let storage_path3 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key3.into());
        overlay_mut
            .insert(storage_path3.full_path(), Some(TrieValue::Storage(U256::from(444).into())));

        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing all changes
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine.set_values(&mut verification_context, &mut [
            (account_path.into(), Some(TrieValue::Account(account))),
            (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(1111).into()))), // Modified
            (storage_path2.full_path(), Some(TrieValue::Storage(U256::from(222).into()))), // Unchanged
            (storage_path3.full_path(), Some(TrieValue::Storage(U256::from(444).into()))), // New
        ]).unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(
            overlay_root, committed_root,
            "Multiple storage overlays same account should match"
        );
    }

    #[test]
    fn test_debug_overlay_vs_committed_single_account() {
        let tmp_dir = TempDir::new("test_debug_overlay_committed_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create one account with 2 storage slots
        let account_address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(account_address);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let storage_key1 = U256::from(10);
        let storage_key2 = U256::from(20);
        let storage_path1 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key1.into());
        let storage_path2 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key2.into());

        // Set up initial state with 2 storage slots
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(111).into()))),
                    (storage_path2.full_path(), Some(TrieValue::Storage(U256::from(222).into()))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Overlay that modifies ONLY ONE storage slot, leaving the other unchanged
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut
            .insert(storage_path1.full_path(), Some(TrieValue::Storage(U256::from(999).into())));
        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing: modify slot1, keep slot2 unchanged
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine.set_values(&mut verification_context, &mut [
            (account_path.into(), Some(TrieValue::Account(account))),
            (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(999).into()))), // Modified
            (storage_path2.full_path(), Some(TrieValue::Storage(U256::from(222).into()))), // Unchanged
        ]).unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(
            overlay_root, committed_root,
            "Single account partial storage overlay should match"
        );
    }

    #[test]
    fn test_multiple_accounts_with_storage_overlays() {
        let tmp_dir = TempDir::new("test_multi_account_storage_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create two accounts with different storage
        let account1_address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account2_address = address!("0x1234567890abcdef1234567890abcdef12345678");

        let account1_path = AddressPath::for_address(account1_address);
        let account2_path = AddressPath::for_address(account2_address);

        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // Storage for account1
        let storage1_key1 = U256::from(10);
        let storage1_key2 = U256::from(20);
        let storage1_path1 =
            crate::path::StoragePath::for_address_and_slot(account1_address, storage1_key1.into());
        let storage1_path2 =
            crate::path::StoragePath::for_address_and_slot(account1_address, storage1_key2.into());

        // Storage for account2
        let storage2_key1 = U256::from(30);
        let storage2_path1 =
            crate::path::StoragePath::for_address_and_slot(account2_address, storage2_key1.into());

        // Set up initial state
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account1_path.clone().into(), Some(TrieValue::Account(account1.clone()))),
                    (account2_path.clone().into(), Some(TrieValue::Account(account2.clone()))),
                    (storage1_path1.full_path(), Some(TrieValue::Storage(U256::from(111).into()))),
                    (storage1_path2.full_path(), Some(TrieValue::Storage(U256::from(222).into()))),
                    (storage2_path1.full_path(), Some(TrieValue::Storage(U256::from(333).into()))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Overlay changes to both accounts' storage
        let mut overlay_mut = OverlayStateMut::new();

        // Modify account1's storage
        overlay_mut
            .insert(storage1_path1.full_path(), Some(TrieValue::Storage(U256::from(1111).into())));

        // Add new storage to account1
        let storage1_key3 = U256::from(40);
        let storage1_path3 =
            crate::path::StoragePath::for_address_and_slot(account1_address, storage1_key3.into());
        overlay_mut
            .insert(storage1_path3.full_path(), Some(TrieValue::Storage(U256::from(444).into())));

        // Modify account2's storage
        overlay_mut
            .insert(storage2_path1.full_path(), Some(TrieValue::Storage(U256::from(3333).into())));

        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing all changes
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context,
                &mut [
                    (account1_path.into(), Some(TrieValue::Account(account1))),
                    (account2_path.into(), Some(TrieValue::Account(account2))),
                    (storage1_path1.full_path(), Some(TrieValue::Storage(U256::from(1111).into()))),
                    (storage1_path2.full_path(), Some(TrieValue::Storage(U256::from(222).into()))),
                    (storage1_path3.full_path(), Some(TrieValue::Storage(U256::from(444).into()))),
                    (storage2_path1.full_path(), Some(TrieValue::Storage(U256::from(3333).into()))),
                ],
            )
            .unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(
            overlay_root, committed_root,
            "Multi-account storage overlay root should match committed root"
        );
    }

    #[test]
    fn test_debug_multi_account_storage() {
        let tmp_dir = TempDir::new("test_debug_multi_account_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create two accounts with very simple, distinct addresses
        let account1_address = address!("0x0000000000000000000000000000000000000001");
        let account2_address = address!("0x0000000000000000000000000000000000000002");

        let account1_path = AddressPath::for_address(account1_address);
        let account2_path = AddressPath::for_address(account2_address);

        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // One storage slot for each account
        let storage1_key = U256::from(10);
        let storage2_key = U256::from(20);
        let storage1_path =
            crate::path::StoragePath::for_address_and_slot(account1_address, storage1_key.into());
        let storage2_path =
            crate::path::StoragePath::for_address_and_slot(account2_address, storage2_key.into());

        // Set up initial state
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account1_path.clone().into(), Some(TrieValue::Account(account1.clone()))),
                    (account2_path.clone().into(), Some(TrieValue::Account(account2.clone()))),
                    (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(111).into()))),
                    (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(222).into()))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Modify just one storage slot for account1
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut
            .insert(storage1_path.full_path(), Some(TrieValue::Storage(U256::from(999).into())));
        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the change
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine.set_values(&mut verification_context, &mut [
            (account1_path.into(), Some(TrieValue::Account(account1))),
            (account2_path.into(), Some(TrieValue::Account(account2))),
            (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(999).into()))), // Modified
            (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(222).into()))), // Unchanged
        ]).unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(
            overlay_root, committed_root,
            "Debug: Simple multi-account storage should match"
        );
    }

    #[test]
    fn test_debug_both_accounts_storage_change() {
        let tmp_dir = TempDir::new("test_debug_both_accounts_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create two accounts with simple addresses
        let account1_address = address!("0x0000000000000000000000000000000000000001");
        let account2_address = address!("0x0000000000000000000000000000000000000002");

        let account1_path = AddressPath::for_address(account1_address);
        let account2_path = AddressPath::for_address(account2_address);

        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // One storage slot for each account
        let storage1_key = U256::from(10);
        let storage2_key = U256::from(20);
        let storage1_path =
            crate::path::StoragePath::for_address_and_slot(account1_address, storage1_key.into());
        let storage2_path =
            crate::path::StoragePath::for_address_and_slot(account2_address, storage2_key.into());

        // Set up initial state
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account1_path.clone().into(), Some(TrieValue::Account(account1.clone()))),
                    (account2_path.clone().into(), Some(TrieValue::Account(account2.clone()))),
                    (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(111).into()))),
                    (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(222).into()))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Modify storage for BOTH accounts
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut
            .insert(storage1_path.full_path(), Some(TrieValue::Storage(U256::from(999).into())));
        overlay_mut
            .insert(storage2_path.full_path(), Some(TrieValue::Storage(U256::from(888).into())));
        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing both changes
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine.set_values(&mut verification_context, &mut [
            (account1_path.into(), Some(TrieValue::Account(account1))),
            (account2_path.into(), Some(TrieValue::Account(account2))),
            (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(999).into()))), // Modified
            (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(888).into()))), // Modified
        ]).unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(
            overlay_root, committed_root,
            "Debug: Both accounts storage changes should match"
        );
    }

    #[test]
    fn test_debug_adding_new_storage_multi_account() {
        let tmp_dir = TempDir::new("test_debug_new_storage_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create two accounts (similar to the original failing test)
        let account1_address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account2_address = address!("0x1234567890abcdef1234567890abcdef12345678");

        let account1_path = AddressPath::for_address(account1_address);
        let account2_path = AddressPath::for_address(account2_address);

        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // Initial storage
        let storage1_key1 = U256::from(10);
        let storage1_path1 =
            crate::path::StoragePath::for_address_and_slot(account1_address, storage1_key1.into());

        // Set up initial state with just one storage slot
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account1_path.clone().into(), Some(TrieValue::Account(account1.clone()))),
                    (account2_path.clone().into(), Some(TrieValue::Account(account2.clone()))),
                    (storage1_path1.full_path(), Some(TrieValue::Storage(U256::from(111).into()))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Add NEW storage to account1
        let mut overlay_mut = OverlayStateMut::new();
        let storage1_key2 = U256::from(40); // New storage key
        let storage1_path2 =
            crate::path::StoragePath::for_address_and_slot(account1_address, storage1_key2.into());

        overlay_mut
            .insert(storage1_path2.full_path(), Some(TrieValue::Storage(U256::from(444).into())));
        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the addition
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine.set_values(&mut verification_context, &mut [
            (account1_path.into(), Some(TrieValue::Account(account1))),
            (account2_path.into(), Some(TrieValue::Account(account2))),
            (storage1_path1.full_path(), Some(TrieValue::Storage(U256::from(111).into()))), // Original
            (storage1_path2.full_path(), Some(TrieValue::Storage(U256::from(444).into()))), // New
        ]).unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(overlay_root, committed_root, "Debug: Adding new storage should match");
    }

    #[test]
    fn test_storage_overlay_with_empty_account() {
        let tmp_dir = TempDir::new("test_empty_account_storage_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create an account with no initial storage
        let account_address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account_path = AddressPath::for_address(account_address);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // Set up initial state with just the account (no storage)
        db.storage_engine
            .set_values(
                &mut context,
                &mut [(account_path.clone().into(), Some(TrieValue::Account(account.clone())))],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Add storage to account that had no storage before
        let mut overlay_mut = OverlayStateMut::new();
        let storage_key = U256::from(42);
        let storage_path =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key.into());
        let storage_value = U256::from(123);
        overlay_mut
            .insert(storage_path.full_path(), Some(TrieValue::Storage(storage_value.into())));
        let overlay = overlay_mut.freeze();

        let overlay_root = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the storage addition
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context,
                &mut [
                    (account_path.into(), Some(TrieValue::Account(account))),
                    (storage_path.full_path(), Some(TrieValue::Storage(storage_value.into()))),
                ],
            )
            .unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(
            overlay_root, committed_root,
            "Empty account storage overlay root should match committed root"
        );
    }
}
