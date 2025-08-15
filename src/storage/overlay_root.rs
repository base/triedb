use crate::{
    account::Account,
    context::TransactionContext,
    node::{Node, NodeKind, TrieValue},
    overlay::{OverlayState, OverlayValue},
    page::{PageId, SlottedPage},
    pointer::Pointer,
    storage::engine::{Error, StorageEngine},
};
use alloy_primitives::{
    map::{B256Map, HashMap},
    B256, U256,
};
use alloy_rlp::{encode, encode_fixed_size};
use alloy_trie::{BranchNodeCompact, HashBuilder, Nibbles, TrieAccount};
use arrayvec::ArrayVec;

#[derive(Debug, Default)]
struct Stats {
    account: AccountStats,
    storage: StorageStats,
}

#[derive(Debug, Default)]
struct AccountStats {
    pointer_hashes: usize,
    branch_nodes: usize,
    leaves: usize,
    overlay_branch_nodes: usize,
    overlay_leaves: usize,
}

#[derive(Debug, Default)]
struct StorageStats {
    branch_nodes: usize,
    leaves: usize,
    overlay_branch_nodes: usize,
    overlay_leaves: usize,
}

impl StorageEngine {
    /// Computes the root hash with overlay changes without persisting them.
    /// This uses alloy-trie's HashBuilder for efficient merkle root computation.
    pub fn compute_root_with_overlay(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
    ) -> Result<
        (B256, HashMap<Nibbles, BranchNodeCompact>, B256Map<HashMap<Nibbles, BranchNodeCompact>>),
        Error,
    > {
        if overlay.is_empty() {
            // No overlay changes, return current root
            return Ok((context.root_node_hash, HashMap::default(), B256Map::default()));
        }

        let mut hash_builder = HashBuilder::default().with_updates(true);
        let mut stats = Stats::default();
        let mut updated_storage_branch_nodes = B256Map::default();

        // Use proper trie traversal with overlay integration
        self.traverse_with_overlay(
            context,
            overlay,
            &mut hash_builder,
            &mut stats,
            &mut updated_storage_branch_nodes,
        )?;

        let (mut hash_builder, updated_branch_nodes) = hash_builder.split();
        // println!("Updated branch nodes: {:?}", updated_branch_nodes);

        let root = hash_builder.root(); // This will clear the hash builder
        println!("Root: {:?}", root);

        println!("Stats: {:?}", stats);
        Ok((root, updated_branch_nodes, updated_storage_branch_nodes))
    }

    /// Helper method to traverse the existing trie and integrate with overlay
    fn traverse_with_overlay(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
        hash_builder: &mut HashBuilder,
        stats: &mut Stats,
        updated_storage_branch_nodes: &mut B256Map<HashMap<Nibbles, BranchNodeCompact>>,
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
                stats,
                updated_storage_branch_nodes,
            )?;
        } else {
            // No root page, just add all overlay changes to the hash builder
            self.process_nonoverlapping_overlay_state(
                context,
                overlay,
                hash_builder,
                stats,
                updated_storage_branch_nodes,
            )?;
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
        stats: &mut Stats,
        updated_storage_branch_nodes: &mut B256Map<HashMap<Nibbles, BranchNodeCompact>>,
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
            stats,
            updated_storage_branch_nodes,
        )
    }

    /// Traverse a specific node with overlayed state.
    /// If this node is a branch, we can add it by hash if there are no overlayed changes under its
    /// path prefix. If this node is a leaf, we can add it if there are no overlayed changes
    /// under its full path. Otherwise, we need to traverse through the node via its full path.
    /// In all cases, we need to process the overlayed state before and after the added or traversed
    /// node path.
    fn traverse_node_with_overlay(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
        hash_builder: &mut HashBuilder,
        slotted_page: &SlottedPage,
        cell_index: u8,
        path_prefix: &Nibbles,
        node_hash: Option<B256>,
        stats: &mut Stats,
        updated_storage_branch_nodes: &mut B256Map<HashMap<Nibbles, BranchNodeCompact>>,
    ) -> Result<(), Error> {
        let node: Node = slotted_page.get_value(cell_index)?;
        let full_path = {
            let mut full = path_prefix.clone();
            full.extend_from_slice_unchecked(node.prefix());
            full
        };

        match node.kind() {
            // if the node is a branch, we can only add it by hash if the path_prefix is completely
            // unaffected by the overlay
            NodeKind::Branch { .. } => {
                // Filter the overlay based on the path_prefix
                let (pre_overlay, with_prefix, post_overlay) =
                    overlay.sub_slice_by_prefix(&path_prefix);
                if with_prefix.is_empty() {
                    self.process_nonoverlapping_overlay_state(
                        context,
                        &pre_overlay,
                        hash_builder,
                        stats,
                        updated_storage_branch_nodes,
                    )?;
                    if !node.prefix().is_empty() {
                        // The node is actually an extension + branch node. We cannot add it by hash
                        // as the extension prefix may have changed, which
                        // would in turn change the hash. We need to
                        // traverse the node via its full path.
                        println!(
                            "Processing extension + branch: {:?} / {:?}",
                            path_prefix, full_path
                        );
                        self.handle_affected_node_with_overlay(
                            context,
                            &with_prefix,
                            hash_builder,
                            slotted_page,
                            &node,
                            &full_path,
                            stats,
                            updated_storage_branch_nodes,
                        )?;
                    } else {
                        // This is a true branch node, so we can add it by hash.
                        let hash = node_hash.unwrap();
                        println!("Adding unaffected branch: {:?}", path_prefix);
                        hash_builder.add_branch(path_prefix.clone(), hash, true);
                        stats.account.branch_nodes += 1;
                        self.process_nonoverlapping_overlay_state(
                            context,
                            &post_overlay,
                            hash_builder,
                            stats,
                            updated_storage_branch_nodes,
                        )?;
                    }
                    return Ok(());
                } else {
                    let (pre_overlay, with_prefix, post_overlay) =
                        overlay.sub_slice_by_prefix(&full_path);
                    self.process_nonoverlapping_overlay_state(
                        context,
                        &pre_overlay,
                        hash_builder,
                        stats,
                        updated_storage_branch_nodes,
                    )?;
                    println!("Processing affected branch: {:?}", path_prefix);
                    self.handle_affected_node_with_overlay(
                        context,
                        &with_prefix,
                        hash_builder,
                        slotted_page,
                        &node,
                        &full_path,
                        stats,
                        updated_storage_branch_nodes,
                    )?;
                    self.process_nonoverlapping_overlay_state(
                        context,
                        &post_overlay,
                        hash_builder,
                        stats,
                        updated_storage_branch_nodes,
                    )?;
                    return Ok(());
                }
            }
            NodeKind::AccountLeaf { .. } | NodeKind::StorageLeaf { .. } => {
                // filter the overlay based on the full_path
                let (pre_overlay, with_prefix, post_overlay) =
                    overlay.sub_slice_by_prefix(&full_path);
                self.process_nonoverlapping_overlay_state(
                    context,
                    &pre_overlay,
                    hash_builder,
                    stats,
                    updated_storage_branch_nodes,
                )?;
                if with_prefix.is_empty() {
                    println!("Adding unaffected leaf: {:?}", full_path);
                    let node_value = node.value()?;
                    let rlp_encoded = self.encode_trie_value(&node_value)?;
                    hash_builder.add_leaf(full_path, &rlp_encoded);
                    stats.account.leaves += 1;
                } else {
                    println!("Processing affected leaf: {:?}", full_path);
                    self.handle_affected_node_with_overlay(
                        context,
                        &with_prefix,
                        hash_builder,
                        slotted_page,
                        &node,
                        &full_path,
                        stats,
                        updated_storage_branch_nodes,
                    )?;
                }
                self.process_nonoverlapping_overlay_state(
                    context,
                    &post_overlay,
                    hash_builder,
                    stats,
                    updated_storage_branch_nodes,
                )?;
                return Ok(());
            }
        }
    }

    fn process_nonoverlapping_overlay_state(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
        hash_builder: &mut HashBuilder,
        stats: &mut Stats,
        updated_storage_branch_nodes: &mut B256Map<HashMap<Nibbles, BranchNodeCompact>>,
    ) -> Result<(), Error> {
        let mut last_processed_path: Option<&[u8]> = None;
        for (path, value) in overlay.iter() {
            if let Some(ref last_processed_path) = last_processed_path {
                if path.starts_with(last_processed_path) {
                    // skip over all descendants of a processed path
                    continue;
                }
            }
            match value {
                Some(OverlayValue::Account(account)) => {
                    self.handle_overlayed_account(
                        context,
                        overlay,
                        hash_builder,
                        &path,
                        account,
                        stats,
                        updated_storage_branch_nodes,
                    )?;
                    last_processed_path = Some(path);
                }
                Some(OverlayValue::Storage(storage_value)) => {
                    let rlp_encoded = self.encode_storage(storage_value)?;
                    println!("Adding overlayed storage leaf: {:?}", path);
                    hash_builder.add_leaf(Nibbles::from_nibbles(path), &rlp_encoded);
                    stats.storage.overlay_leaves += 1;
                    last_processed_path = Some(path);
                }
                Some(OverlayValue::Hash(hash)) => {
                    println!("Adding overlayed branch: {:?}", path);
                    hash_builder.add_branch(Nibbles::from_nibbles(path), *hash, false);
                    stats.account.overlay_branch_nodes += 1;
                    last_processed_path = Some(path);
                }
                None => {
                    // Tombstone - skip
                    println!("Skipping tombstone: {:?}", path);
                    last_processed_path = Some(path);
                }
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
        stats: &mut Stats,
        updated_storage_branch_nodes: &mut B256Map<HashMap<Nibbles, BranchNodeCompact>>,
    ) -> Result<(), Error> {
        match node.kind() {
            NodeKind::Branch { .. } => {
                self.traverse_branch_node_with_overlay(
                    context,
                    overlay,
                    hash_builder,
                    slotted_page,
                    node,
                    full_path,
                    stats,
                    updated_storage_branch_nodes,
                )?;
            }
            NodeKind::AccountLeaf { .. } => {
                // Account leaf with descendant storage overlays
                self.traverse_account_leaf_with_overlayed_storage(
                    context,
                    overlay,
                    hash_builder,
                    slotted_page,
                    Some(node),
                    full_path,
                    stats,
                    updated_storage_branch_nodes,
                )?;
            }
            NodeKind::StorageLeaf { .. } => match overlay.get(0) {
                Some((_, Some(OverlayValue::Storage(value)))) => {
                    hash_builder.add_leaf(full_path.clone(), &self.encode_storage(value)?);
                    stats.storage.overlay_leaves += 1;
                }
                Some((_, None)) => {
                    println!("Skipping deleted storage leaf: {:?}", full_path);
                    stats.storage.overlay_leaves += 1;
                }
                _ => {
                    panic!("Storage leaf does not have a valid overlay: {full_path:?}");
                }
            },
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
        stats: &mut Stats,
        updated_storage_branch_nodes: &mut B256Map<HashMap<Nibbles, BranchNodeCompact>>,
    ) -> Result<(), Error> {
        // For each child in the branch node (0-15), check if there are relevant overlay changes
        // and recursively traverse child nodes.
        // As long as there will be at least 2 children, this branch will still exist, allowing us
        // to add the children by hash instead of traversing them.

        let mut children: [(Nibbles, OverlayState, Option<&Pointer>); 16] =
            std::array::from_fn(|_| (Nibbles::default(), OverlayState::empty(), None::<&Pointer>));
        for i in 0..16 {
            let mut child_path = full_path.clone();
            child_path.push(i);

            // Create sub-slice of overlay for this child's subtree
            let child_overlay = overlay.sub_slice_for_prefix(&child_path);

            children[i as usize] = (child_path, child_overlay, node.child(i as u8).unwrap());
        }

        // This conservatively counts the minimum number of children that will exist. It may
        // undercount.
        let min_num_children = children
            .iter()
            .filter(|(_, child_overlay, child_pointer)| {
                if let Some((_, value)) = child_overlay.get(0) {
                    // If the overlayed value is none, this branch path might be removed.
                    return value.is_some();
                } else if child_pointer.is_some() {
                    // If there is no overlayed value and an existing child, then this path will
                    // definitely exist.
                    return true;
                }

                false
            })
            .count();

        if min_num_children > 1 {
            // We are guaranteed to have at least 2 children, keeping this branch node alive.
            // We can add non-overlayed children by hash instead of traversing them. This can save
            // many lookups, hashes, and page reads.
            for (child_path, child_overlay, child_pointer) in children.iter() {
                if let Some((path, _)) = child_overlay.get(0) {
                    if path == child_path.as_slice() {
                        self.process_nonoverlapping_overlay_state(
                            context,
                            &child_overlay,
                            hash_builder,
                            stats,
                            updated_storage_branch_nodes,
                        )?;
                        continue;
                    }
                }

                if let Some(child_pointer) = child_pointer {
                    let child_hash = child_pointer.rlp().as_hash();
                    if child_overlay.is_empty() && child_hash.is_some() {
                        println!("Adding branch node by pointer: {:?}", child_path);
                        hash_builder.add_branch(child_path.clone(), child_hash.unwrap(), true);
                        stats.account.pointer_hashes += 1;
                    } else {
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
                                stats,
                                updated_storage_branch_nodes,
                            )?;
                        } else if let Some(child_page_id) = child_location.page_id() {
                            // Child is in a different page
                            self.traverse_page_with_overlay(
                                context,
                                &child_overlay,
                                hash_builder,
                                child_page_id,
                                &child_path,
                                child_hash,
                                stats,
                                updated_storage_branch_nodes,
                            )?;
                        }
                    }
                } else {
                    // No child exists on disk, process any matching overlay changes
                    self.process_nonoverlapping_overlay_state(
                        context,
                        &child_overlay,
                        hash_builder,
                        stats,
                        updated_storage_branch_nodes,
                    )?;
                }
            }
            return Ok(());
        }

        // Otherwise, it is possible that this branch might be removed.
        // We need to traverse and add the children directly in order to be safe.
        for (child_path, child_overlay, child_pointer) in children.iter() {
            if let Some((path, _)) = child_overlay.get(0) {
                if path == child_path.as_slice() {
                    // Direct overlay - the overlay path exactly matches this node's path
                    // No need to traverse the child
                    self.process_nonoverlapping_overlay_state(
                        context,
                        &child_overlay,
                        hash_builder,
                        stats,
                        updated_storage_branch_nodes,
                    )?;
                    continue;
                }
            }

            if let Some(child_pointer) = child_pointer {
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
                        stats,
                        updated_storage_branch_nodes,
                    )?;
                } else if let Some(child_page_id) = child_location.page_id() {
                    // Child is in a different page
                    self.traverse_page_with_overlay(
                        context,
                        &child_overlay,
                        hash_builder,
                        child_page_id,
                        &child_path,
                        child_hash,
                        stats,
                        updated_storage_branch_nodes,
                    )?;
                }
            } else {
                // No child exists on disk, process any matching overlay changes
                self.process_nonoverlapping_overlay_state(
                    context,
                    &child_overlay,
                    hash_builder,
                    stats,
                    updated_storage_branch_nodes,
                )?;
            }
        }
        Ok(())
    }

    /// Handle an account leaf with potential storage overlays using iterative HashBuilder approach
    fn traverse_account_leaf_with_overlayed_storage(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
        hash_builder: &mut HashBuilder,
        slotted_page: &SlottedPage,
        node: Option<&Node>,
        full_path: &Nibbles,
        stats: &mut Stats,
        updated_storage_branch_nodes: &mut B256Map<HashMap<Nibbles, BranchNodeCompact>>,
    ) -> Result<(), Error> {
        // Get the original account from the node
        let original_account = node.map(|n| match n.value().unwrap() {
            TrieValue::Account(account) => account,
            _ => {
                panic!("Node is not an account leaf");
            }
        });

        // Check if this account is directly overlaid (account-level changes)
        let account = if let Some(overlay_value) = overlay.lookup(full_path) {
            // Direct account overlay - use overlay value, but still check for storage overlays
            if let Some(trie_value) = overlay_value {
                // Even with account overlay, we might need to compute storage root for storage
                // overlays
                if let OverlayValue::Account(overlay_account) = trie_value {
                    stats.account.overlay_leaves += 1;
                    Some(overlay_account)
                } else {
                    panic!("Overlay value is not an account");
                }
            } else {
                // If overlay_value is None, it's a deletion - skip
                println!("Skipping deleted account: {full_path:?}");
                None
            }
        } else {
            stats.account.leaves += 1;
            original_account.as_ref()
        };

        if let Some(account) = account {
            // Check if there are any storage overlays for this account
            // Storage overlays have 128-nibble paths that start with this account's 64-nibble path
            let storage_overlays = overlay.sub_slice_for_prefix(full_path);
            let has_storage_overlays = storage_overlays.iter().any(|(path, _)| path.len() > 64);

            if !has_storage_overlays {
                // No storage overlays for this account, use original account
                let rlp_encoded = self.encode_account(account)?;
                println!("Adding account leaf: {full_path:?}");
                hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
                return Ok(());
            }

            // We have storage overlays, need to compute a new storage root using iterative approach
            let (new_storage_root, updated_branch_nodes) = self.compute_storage_root_with_overlay(
                context,
                node,
                &storage_overlays,
                slotted_page,
                stats,
                updated_storage_branch_nodes,
            )?;
            updated_storage_branch_nodes
                .insert(B256::from_slice(&full_path.pack()), updated_branch_nodes);

            // Add the modified account to the main HashBuilder
            println!("Adding modified account leaf: {full_path:?} with storage root: {new_storage_root:?}");
            let rlp_encoded = self.encode_account_with_root(account, new_storage_root)?;
            hash_builder.add_leaf(full_path.clone(), &rlp_encoded);
        }
        Ok(())
    }

    fn handle_overlayed_account(
        &self,
        context: &TransactionContext,
        overlay: &OverlayState,
        hash_builder: &mut HashBuilder,
        full_path: &[u8],
        account: &Account,
        stats: &mut Stats,
        updated_storage_branch_nodes: &mut B256Map<HashMap<Nibbles, BranchNodeCompact>>,
    ) -> Result<(), Error> {
        println!("Handling overlayed account: {full_path:?}");
        println!("Account: {account:?}");
        // Check if there are any storage overlays for this account
        // Storage overlays have 128-nibble paths that start with this account's 64-nibble path
        let storage_overlays = overlay.sub_slice_for_prefix(full_path);
        let has_storage_overlays = storage_overlays.iter().any(|(path, _)| path.len() > 64);

        if !has_storage_overlays {
            // No storage overlays for this account, use original account
            let rlp_encoded = self.encode_account(account)?;
            // println!("Adding overlayed account leaf: {:?}", full_path);
            hash_builder.add_leaf(Nibbles::from_nibbles(full_path), &rlp_encoded);
            stats.account.overlay_leaves += 1;
            return Ok(());
        }

        // We have storage overlays, need to compute a new storage root
        let storage_overlay = storage_overlays.with_prefix_offset(64);

        let mut storage_hash_builder = HashBuilder::default().with_updates(true);

        self.process_nonoverlapping_overlay_state(
            context,
            &storage_overlay,
            &mut storage_hash_builder,
            stats,
            updated_storage_branch_nodes,
        )?;

        let (mut storage_hash_builder, updated_branch_nodes) = storage_hash_builder.split();
        let new_storage_root = storage_hash_builder.root();
        println!("New storage root: {new_storage_root:?}");
        updated_storage_branch_nodes.insert(
            B256::from_slice(&Nibbles::from_nibbles(full_path).pack()),
            updated_branch_nodes,
        );

        // Add the modified account to the main HashBuilder
        let rlp_encoded = self.encode_account_with_root(account, new_storage_root)?;
        hash_builder.add_leaf(Nibbles::from_nibbles(full_path), &rlp_encoded);
        stats.account.overlay_leaves += 1;

        Ok(())
    }

    /// Compute the storage root for an account using iterative HashBuilder approach with prefix
    /// offset
    fn compute_storage_root_with_overlay(
        &self,
        context: &TransactionContext,
        account_node: Option<&Node>,
        storage_overlays: &OverlayState,
        slotted_page: &SlottedPage,
        stats: &mut Stats,
        updated_storage_branch_nodes: &mut B256Map<HashMap<Nibbles, BranchNodeCompact>>,
    ) -> Result<(B256, HashMap<Nibbles, BranchNodeCompact>), Error> {
        // Create a storage-specific overlay with 64-nibble prefix offset
        // This converts 128-nibble storage paths to 64-nibble storage-relative paths
        let mut storage_overlay = storage_overlays.with_prefix_offset(64);
        if let Some((_, Some(OverlayValue::Account(_)))) = storage_overlay.get(0) {
            // println!("Skipping account overlay: {:?}", path);
            storage_overlay = storage_overlay.sub_slice(1, storage_overlay.len());
        }

        let mut storage_hash_builder = HashBuilder::default().with_updates(true);

        // Get the original account's storage root to determine if we need to traverse existing
        // storage
        let original_storage_root = account_node
            .map(|n| match n.value().unwrap() {
                TrieValue::Account(account) => account.storage_root,
                _ => panic!("Node is not an account leaf"), /* This shouldn't happen for account
                                                             * nodes */
            })
            .unwrap_or(alloy_trie::EMPTY_ROOT_HASH);

        // If the account has existing storage, traverse the existing storage trie
        if original_storage_root != alloy_trie::EMPTY_ROOT_HASH {
            // Try to find the storage root page from the account node's direct child
            if let Ok(Some(storage_root_pointer)) = account_node.unwrap().direct_child() {
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
                        stats,
                        updated_storage_branch_nodes,
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
                        stats,
                        updated_storage_branch_nodes,
                    )?;
                }
            }
        } else {
            // No existing storage, just add overlay changes
            self.process_nonoverlapping_overlay_state(
                context,
                &storage_overlay,
                &mut storage_hash_builder,
                stats,
                updated_storage_branch_nodes,
            )?;
        }

        let (mut storage_hash_builder, updated_branch_nodes) = storage_hash_builder.split();
        // println!("Updated storage branch nodes: {updated_branch_nodes:?}");

        let computed_root = storage_hash_builder.root();
        // println!("Computed storage root: {computed_root:?}");
        Ok((computed_root, updated_branch_nodes))
    }

    /// Helper to encode TrieValue as RLP
    #[inline]
    pub fn encode_trie_value(&self, trie_value: &TrieValue) -> Result<Vec<u8>, Error> {
        let rlp_encoded = match trie_value {
            TrieValue::Account(account) => self.encode_account(account)?.to_vec(),
            TrieValue::Storage(storage_value) => self.encode_storage(storage_value)?.to_vec(),
        };
        Ok(rlp_encoded)
    }

    #[inline]
    pub fn encode_account(&self, account: &Account) -> Result<ArrayVec<u8, 110>, Error> {
        let trie_account = Account {
            nonce: account.nonce,
            balance: account.balance,
            storage_root: account.storage_root,
            code_hash: account.code_hash,
        };
        Ok(encode_fixed_size(&trie_account))
    }

    #[inline]
    pub fn encode_account_with_root(
        &self,
        account: &Account,
        root: B256,
    ) -> Result<ArrayVec<u8, 110>, Error> {
        let trie_account = Account {
            nonce: account.nonce,
            balance: account.balance,
            storage_root: root,
            code_hash: account.code_hash,
        };
        Ok(encode_fixed_size(&trie_account))
    }

    #[inline]
    pub fn encode_storage(&self, storage_value: &U256) -> Result<ArrayVec<u8, 33>, Error> {
        Ok(encode_fixed_size(storage_value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        account::Account, database::Database, node::TrieValue, overlay::OverlayStateMut,
        path::AddressPath,
    };
    use alloy_primitives::{address, Address, U256};
    use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
    use rand::Rng;
    use tempdir::TempDir;
    use test_log::test;

    #[test]
    fn test_empty_overlay_root() {
        let tmp_dir = TempDir::new("test_overlay_root_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let context = db.storage_engine.read_context();
        let empty_overlay = OverlayStateMut::new().freeze();

        let (root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &empty_overlay).unwrap();
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

        overlay_mut.insert(address_path.into(), Some(OverlayValue::Account(account)));
        let overlay = overlay_mut.freeze();

        // Compute root with overlay
        let (root, _, _) = db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();

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
        let (root_with_empty_overlay, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &empty_overlay).unwrap();
        assert_eq!(root_with_empty_overlay, initial_root);

        // Now test with actual overlay changes - modify the same account with different values
        let mut overlay_mut = OverlayStateMut::new();
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        overlay_mut
            .insert(address_path.clone().into(), Some(OverlayValue::Account(account2.clone())));
        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
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
            .insert(path1.clone().into(), Some(OverlayValue::Account(account1_updated.clone())));
        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
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
        overlay_mut2.insert(path3.clone().into(), Some(OverlayValue::Account(account3.clone())));
        let overlay2 = overlay_mut2.freeze();

        let (overlay_root2, _, _) =
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
            .insert(path1.clone().into(), Some(OverlayValue::Account(account1_updated.clone()))); // Modify existing
        overlay_mut3.insert(path3.clone().into(), Some(OverlayValue::Account(account3.clone()))); // Create new
                                                                                                  // path2 is left unaffected - should use add_branch optimization
        let overlay3 = overlay_mut3.freeze();

        let (overlay_root3, _, _) =
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
        let mut context = db.storage_engine.write_context();
        let path1 = AddressPath::new(Nibbles::from_nibbles([
            0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        ]));
        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // Step 2: Add account 2
        let path2 = AddressPath::new(Nibbles::from_nibbles([
            0x1, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        ]));
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // Step 3: Add account 3
        let path3 = AddressPath::new(Nibbles::from_nibbles([
            0x2, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        ]));
        let account3 = Account::new(3, U256::from(300), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (path1.clone().into(), Some(TrieValue::Account(account1.clone()))),
                    (path3.clone().into(), Some(TrieValue::Account(account3.clone()))),
                ],
            )
            .unwrap();
        let root_without_account2 = context.root_node_hash;

        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (path1.clone().into(), Some(TrieValue::Account(account1.clone()))),
                    (path2.clone().into(), Some(TrieValue::Account(account2.clone()))),
                    (path3.clone().into(), Some(TrieValue::Account(account3.clone()))),
                ],
            )
            .unwrap();
        let root_with_all_accounts = context.root_node_hash;
        assert_ne!(root_with_all_accounts, root_without_account2);

        // Step 4: Overlay a tombstone for account 2 and compute root
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(path2.clone().into(), None); // Delete account2
        let overlay = overlay_mut.freeze();

        let (overlay_root_with_deletion, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root_with_deletion, root_with_all_accounts);

        // Step 4: Verify by actually erasing account 2 and computing root
        db.storage_engine.set_values(&mut context, &mut [(path2.clone().into(), None)]).unwrap();
        let root_after_deletion = context.root_node_hash;

        // The overlay root with tombstone should match the root after actual deletion
        assert_eq!(
            overlay_root_with_deletion, root_after_deletion,
            "Tombstone overlay root should match actual deletion root"
        );

        // Both should equal the original root with just account1
        assert_eq!(
            overlay_root_with_deletion, root_without_account2,
            "After deleting account2, root should match original single-account root"
        );
        assert_eq!(
            root_after_deletion, root_without_account2,
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
                    (storage_path1.full_path(), Some(TrieValue::Storage(storage_value1))),
                    (storage_path2.full_path(), Some(TrieValue::Storage(storage_value2))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;
        assert_ne!(initial_root, EMPTY_ROOT_HASH);

        // Test Case 1: Overlay that modifies existing storage
        let mut overlay_mut = OverlayStateMut::new();
        let new_storage_value1 = U256::from(999);
        overlay_mut
            .insert(storage_path1.full_path(), Some(OverlayValue::Storage(new_storage_value1)));
        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the storage change
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context,
                &mut [
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.full_path(), Some(TrieValue::Storage(new_storage_value1))),
                    (storage_path2.full_path(), Some(TrieValue::Storage(storage_value2))),
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
        overlay_mut2.insert(storage_path3.full_path(), Some(OverlayValue::Storage(storage_value3)));
        let overlay2 = overlay_mut2.freeze();

        let (overlay_root2, _, _) =
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
                    (storage_path1.full_path(), Some(TrieValue::Storage(storage_value1))),
                    (storage_path2.full_path(), Some(TrieValue::Storage(storage_value2))),
                    (storage_path3.full_path(), Some(TrieValue::Storage(storage_value3))),
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

        let (overlay_root3, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay3).unwrap();
        assert_ne!(overlay_root3, initial_root);

        // Verify by committing the deletion
        let mut verification_context3 = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context3,
                &mut [
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.full_path(), Some(TrieValue::Storage(storage_value1))),
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
        overlay_mut4.insert(
            account_path.clone().into(),
            Some(OverlayValue::Account(updated_account.clone())),
        );
        overlay_mut4
            .insert(storage_path1.full_path(), Some(OverlayValue::Storage(new_storage_value1)));
        let overlay4 = overlay_mut4.freeze();

        let (overlay_root4, _, _) =
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
        overlay_mut.insert(
            modify_path.clone().into(),
            Some(OverlayValue::Account(updated_account.clone())),
        );
        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
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

        // println!("Storage path 1: {:?}", storage_path1.full_path());

        // Set up initial state with 1 storage slot
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(111)))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Add a NEW storage slot via overlay
        let mut overlay_mut = OverlayStateMut::new();
        let storage_key2 = U256::from(20); // New storage key
        let storage_path2 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key2.into());

        // println!("Storage path 2: {:?}", storage_path2.full_path());

        overlay_mut.insert(storage_path2.full_path(), Some(OverlayValue::Storage(U256::from(222))));
        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the addition
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine.set_values(&mut verification_context, &mut [
            (account_path.into(), Some(TrieValue::Account(account))),
            (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(111)))), // Original
            (storage_path2.full_path(), Some(TrieValue::Storage(U256::from(222)))), // New
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
                    (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(111)))),
                    (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(222)))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Modify just one storage value per account via overlay
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage1_path.full_path(), Some(OverlayValue::Storage(U256::from(999))));
        overlay_mut.insert(storage2_path.full_path(), Some(OverlayValue::Storage(U256::from(888))));
        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the changes
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context,
                &mut [
                    (account1_path.into(), Some(TrieValue::Account(account1))),
                    (account2_path.into(), Some(TrieValue::Account(account2))),
                    (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(999)))),
                    (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(888)))),
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
                    (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(111)))),
                    (storage_path2.full_path(), Some(TrieValue::Storage(U256::from(222)))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Apply MULTIPLE storage overlays to the same account
        let mut overlay_mut = OverlayStateMut::new();

        // Modify existing storage slot 1
        overlay_mut
            .insert(storage_path1.full_path(), Some(OverlayValue::Storage(U256::from(1111))));

        // Add new storage slot 3
        let storage_key3 = U256::from(40);
        let storage_path3 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key3.into());
        overlay_mut.insert(storage_path3.full_path(), Some(OverlayValue::Storage(U256::from(444))));

        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing all changes
        db.storage_engine.set_values(&mut context, &mut [
            (account_path.into(), Some(TrieValue::Account(account))),
            (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(1111)))), // Modified
            (storage_path2.full_path(), Some(TrieValue::Storage(U256::from(222)))), // Unchanged
            (storage_path3.full_path(), Some(TrieValue::Storage(U256::from(444)))), // New
        ]).unwrap();
        let committed_root = context.root_node_hash;

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
                    (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(111)))),
                    (storage_path2.full_path(), Some(TrieValue::Storage(U256::from(222)))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Overlay that modifies ONLY ONE storage slot, leaving the other unchanged
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage_path1.full_path(), Some(OverlayValue::Storage(U256::from(999))));
        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing: modify slot1, keep slot2 unchanged
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine.set_values(&mut verification_context, &mut [
            (account_path.into(), Some(TrieValue::Account(account))),
            (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(999)))), // Modified
            (storage_path2.full_path(), Some(TrieValue::Storage(U256::from(222)))), // Unchanged
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
                    (storage1_path1.full_path(), Some(TrieValue::Storage(U256::from(111)))),
                    (storage1_path2.full_path(), Some(TrieValue::Storage(U256::from(222)))),
                    (storage2_path1.full_path(), Some(TrieValue::Storage(U256::from(333)))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Overlay changes to both accounts' storage
        let mut overlay_mut = OverlayStateMut::new();

        // Modify account1's storage
        overlay_mut
            .insert(storage1_path1.full_path(), Some(OverlayValue::Storage(U256::from(1111))));

        // Add new storage to account1
        let storage1_key3 = U256::from(40);
        let storage1_path3 =
            crate::path::StoragePath::for_address_and_slot(account1_address, storage1_key3.into());
        overlay_mut
            .insert(storage1_path3.full_path(), Some(OverlayValue::Storage(U256::from(444))));

        // Modify account2's storage
        overlay_mut
            .insert(storage2_path1.full_path(), Some(OverlayValue::Storage(U256::from(3333))));

        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing all changes
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context,
                &mut [
                    (account1_path.into(), Some(TrieValue::Account(account1))),
                    (account2_path.into(), Some(TrieValue::Account(account2))),
                    (storage1_path1.full_path(), Some(TrieValue::Storage(U256::from(1111)))),
                    (storage1_path2.full_path(), Some(TrieValue::Storage(U256::from(222)))),
                    (storage1_path3.full_path(), Some(TrieValue::Storage(U256::from(444)))),
                    (storage2_path1.full_path(), Some(TrieValue::Storage(U256::from(3333)))),
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
                    (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(111)))),
                    (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(222)))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Modify just one storage slot for account1
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage1_path.full_path(), Some(OverlayValue::Storage(U256::from(999))));
        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the change
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine.set_values(&mut verification_context, &mut [
            (account1_path.into(), Some(TrieValue::Account(account1))),
            (account2_path.into(), Some(TrieValue::Account(account2))),
            (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(999)))), // Modified
            (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(222)))), // Unchanged
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
                    (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(111)))),
                    (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(222)))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        // Test: Modify storage for BOTH accounts
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage1_path.full_path(), Some(OverlayValue::Storage(U256::from(999))));
        overlay_mut.insert(storage2_path.full_path(), Some(OverlayValue::Storage(U256::from(888))));
        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing both changes
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine.set_values(&mut verification_context, &mut [
            (account1_path.into(), Some(TrieValue::Account(account1))),
            (account2_path.into(), Some(TrieValue::Account(account2))),
            (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(999)))), // Modified
            (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(888)))), // Modified
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
                    (storage1_path1.full_path(), Some(TrieValue::Storage(U256::from(111)))),
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
            .insert(storage1_path2.full_path(), Some(OverlayValue::Storage(U256::from(444))));
        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the addition
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine.set_values(&mut verification_context, &mut [
            (account1_path.into(), Some(TrieValue::Account(account1))),
            (account2_path.into(), Some(TrieValue::Account(account2))),
            (storage1_path1.full_path(), Some(TrieValue::Storage(U256::from(111)))), // Original
            (storage1_path2.full_path(), Some(TrieValue::Storage(U256::from(444)))), // New
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
        overlay_mut.insert(storage_path.full_path(), Some(OverlayValue::Storage(storage_value)));
        let overlay = overlay_mut.freeze();

        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the storage addition
        let mut verification_context = db.storage_engine.write_context();
        db.storage_engine
            .set_values(
                &mut verification_context,
                &mut [
                    (account_path.into(), Some(TrieValue::Account(account))),
                    (storage_path.full_path(), Some(TrieValue::Storage(storage_value))),
                ],
            )
            .unwrap();
        let committed_root = verification_context.root_node_hash;

        assert_eq!(
            overlay_root, committed_root,
            "Empty account storage overlay root should match committed root"
        );
    }

    #[test]
    fn test_1000_accounts_with_10_overlay() {
        for _ in 0..100 {
            let tmp_dir = TempDir::new("test_1000_accounts_with_10_overlay").unwrap();
            let file_path = tmp_dir.path().join("test.db");
            let db = Database::create_new(file_path).unwrap();

            let mut context = db.storage_engine.write_context();
            let mut rng = rand::rng();

            let mut changes: Vec<(Nibbles, Option<TrieValue>)> = Vec::with_capacity(1000);

            for i in 0..10000 {
                let account_address = Address::random();
                let account =
                    Account::new(i, U256::from(rng.random::<u64>()), EMPTY_ROOT_HASH, KECCAK_EMPTY);
                let account_path = AddressPath::for_address(account_address);

                changes.push((account_path.into(), Some(TrieValue::Account(account))));
            }

            changes.sort_by(|a, b| a.0.cmp(&b.0));

            db.storage_engine.set_values(&mut context, &mut changes).unwrap();

            let initial_root = context.root_node_hash;

            // Create overlay with modifications to every 100th account
            let mut overlay_mut = OverlayStateMut::new();

            // Take every 100th account from the changes
            for (i, (path, value)) in changes.iter().step_by(100).enumerate() {
                if let Some(TrieValue::Account(account)) = value {
                    if i % 2 == 0 {
                        // For half of the sampled accounts, create new modified account
                        let mut new_account = account.clone();
                        new_account.balance = U256::from(rng.random::<u64>()); // Random new balance
                        overlay_mut.insert(path.clone(), Some(OverlayValue::Account(new_account)));
                    } else {
                        // For other half, mark for deletion
                        overlay_mut.insert(path.clone(), None);
                    }
                }
            }

            let mut overlay_mut_with_branches = overlay_mut.clone();
            let overlay = overlay_mut.freeze();

            let (overlay_root, overlay_branches, _) =
                db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
            assert_ne!(overlay_root, initial_root);

            for (path, branch) in overlay_branches.iter() {
                if let Some(root_hash) = branch.root_hash {
                    overlay_mut_with_branches
                        .insert(path.clone(), Some(OverlayValue::Hash(root_hash)));
                }
                let mut hash_idx = 0;
                let mut path = path.clone();
                for i in 0..16 {
                    if branch.hash_mask.is_bit_set(i) {
                        path.push(i);
                        overlay_mut_with_branches.insert(
                            path.clone(),
                            Some(OverlayValue::Hash(branch.hashes[hash_idx])),
                        );
                        hash_idx += 1;
                        path.pop();
                    }
                }
            }
            let overlay_with_branches = overlay_mut_with_branches.freeze();
            // println!("Overlay with branches: {:?}", overlay_with_branches);
            let (overlay_root_with_branches, _, _) = db
                .storage_engine
                .compute_root_with_overlay(&context, &overlay_with_branches)
                .unwrap();
            assert_eq!(overlay_root_with_branches, overlay_root);

            // Verify by committing the storage addition
            let mut changes: Vec<(Nibbles, Option<TrieValue>)> = overlay
                .data()
                .iter()
                .map(|(path, value)| (path.clone(), value.clone().map(|v| v.try_into().unwrap())))
                .collect();
            db.storage_engine.set_values(&mut context, &mut changes).unwrap();
            let committed_root = context.root_node_hash;

            // db.storage_engine
            //     .print_page(&context, std::io::stdout(), context.root_node_page_id)
            //     .unwrap();

            assert_eq!(overlay_root, committed_root, "1000 accounts with 10 overlay should match");
        }
    }

    #[test]
    fn test_overlay_new_account_with_storage() {
        let tmp_dir = TempDir::new("test_overlay_new_account_with_storage").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        let account_address = Address::random();
        let account_path = AddressPath::for_address(account_address);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        db.storage_engine
            .set_values(
                &mut context,
                &mut [(account_path.clone().into(), Some(TrieValue::Account(account.clone())))],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        let mut overlay_mut = OverlayStateMut::new();
        let new_address = Address::random();
        let new_account_path = AddressPath::for_address(new_address);
        let new_account = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        overlay_mut
            .insert(new_account_path.into(), Some(OverlayValue::Account(new_account.clone())));

        let storage_key = U256::from(42);
        let storage_path =
            crate::path::StoragePath::for_address_and_slot(new_address, storage_key.into());
        let storage_value = U256::from(123);
        overlay_mut.insert(storage_path.full_path(), Some(OverlayValue::Storage(storage_value)));

        let overlay = overlay_mut.freeze();
        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the storage addition
        let mut changes: Vec<(Nibbles, Option<TrieValue>)> = overlay
            .data()
            .iter()
            .map(|(path, value)| (path.clone(), value.clone().map(|v| v.try_into().unwrap())))
            .collect();
        db.storage_engine.set_values(&mut context, &mut changes).unwrap();
        let committed_root = context.root_node_hash;

        assert_eq!(overlay_root, committed_root, "Overlay new account with storage should match");
    }

    #[test]
    fn test_overlay_update_account_with_storage() {
        let tmp_dir = TempDir::new("test_overlay_update_account_with_storage").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        let account_address = Address::random();
        let account_path = AddressPath::for_address(account_address);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let storage_key1 = U256::from(42);
        let storage_key2 = U256::from(43);
        let storage_path1 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key1.into());
        let storage_path2 =
            crate::path::StoragePath::for_address_and_slot(account_address, storage_key2.into());

        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.full_path(), Some(TrieValue::Storage(U256::from(111)))),
                    (storage_path2.full_path(), Some(TrieValue::Storage(U256::from(222)))),
                ],
            )
            .unwrap();

        let initial_root = context.root_node_hash;

        let mut overlay_mut = OverlayStateMut::new();
        let new_account = Account::new(1, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        overlay_mut.insert(account_path.clone().into(), Some(OverlayValue::Account(new_account)));
        overlay_mut.insert(storage_path1.full_path(), Some(OverlayValue::Storage(U256::from(333))));

        let overlay = overlay_mut.freeze();
        let (overlay_root, _, _) =
            db.storage_engine.compute_root_with_overlay(&context, &overlay).unwrap();
        assert_ne!(overlay_root, initial_root);

        // Verify by committing the storage addition
        let mut changes: Vec<(Nibbles, Option<TrieValue>)> = overlay
            .data()
            .iter()
            .map(|(path, value)| (path.clone(), value.clone().map(|v| v.try_into().unwrap())))
            .collect();
        db.storage_engine.set_values(&mut context, &mut changes).unwrap();
        let committed_root = context.root_node_hash;

        assert_eq!(
            overlay_root, committed_root,
            "Overlay update account with storage should match"
        );
    }

    #[test]
    fn test_branch_node_prefix_ordering_bug() {
        let tmp_dir = TempDir::new("test_branch_prefix_ordering").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create the specific account path that causes the issue
        // Account path: 0x1dfdadc9cfa121d06649309ad0233f7c14e54b7df756a84e7340eaf8b9912261
        let account_nibbles = Nibbles::from_nibbles([
            0x1, 0xd, 0xf, 0xd, 0xa, 0xd, 0xc, 0x9, 0xc, 0xf, 0xa, 0x1, 0x2, 0x1, 0xd, 0x0, 0x6,
            0x6, 0x4, 0x9, 0x3, 0x0, 0x9, 0xa, 0xd, 0x0, 0x2, 0x3, 0x3, 0xf, 0x7, 0xc, 0x1, 0x4,
            0xe, 0x5, 0x4, 0xb, 0x7, 0xd, 0xf, 0x7, 0x5, 0x6, 0xa, 0x8, 0x4, 0xe, 0x7, 0x3, 0x4,
            0x0, 0xe, 0xa, 0xf, 0x8, 0xb, 0x9, 0x9, 0x1, 0x2, 0x2, 0x6, 0x1,
        ]);
        let account_path = AddressPath::new(account_nibbles);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // Create storage paths that will create a branch node with prefix 0x340
        // These paths are designed to create a branch at storage path 0x340 with children at:
        // - 0x340123aa...aa
        // - 0x340123bb...bb
        // - 0x3411...11

        // First storage path: 0x340123aa...aa (remaining 60 nibbles are 'a')
        let mut storage1_nibbles = vec![0x3, 0x4, 0x0, 0x0, 0x0, 0x0]; // 6 nibbles
        storage1_nibbles.extend(vec![0xa; 58]); // Fill remaining 58 nibbles with 'a' to make 64 total
        let storage1_path = crate::path::StoragePath::for_address_path_and_slot_hash(
            account_path.clone(),
            Nibbles::from_nibbles(storage1_nibbles),
        );

        // Second storage path: 0x340123bb...bb (remaining 60 nibbles are 'b')
        let mut storage2_nibbles = vec![0x3, 0x4, 0x0, 0x0, 0x0, 0x0]; // 6 nibbles
        storage2_nibbles.extend(vec![0xb; 58]); // Fill remaining 58 nibbles with 'b' to make 64 total
        let storage2_path = crate::path::StoragePath::for_address_path_and_slot_hash(
            account_path.clone(),
            Nibbles::from_nibbles(storage2_nibbles),
        );

        // Third storage path: 0x3411...11 (remaining 62 nibbles are '1')
        let mut storage3_nibbles = vec![0x3, 0x4, 0x1]; // 3 nibbles
        storage3_nibbles.extend(vec![0x1; 61]); // Fill remaining 61 nibbles with '1' to make 64 total
        let storage3_path = crate::path::StoragePath::for_address_path_and_slot_hash(
            account_path.clone(),
            Nibbles::from_nibbles(storage3_nibbles),
        );

        // Set up initial state with the account and storage that creates the branch structure
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage1_path.full_path(), Some(TrieValue::Storage(U256::from(111)))),
                    (storage2_path.full_path(), Some(TrieValue::Storage(U256::from(222)))),
                    (storage3_path.full_path(), Some(TrieValue::Storage(U256::from(333)))),
                ],
            )
            .unwrap();

        // Now create an overlay that adds a storage value that will cause the ordering issue
        // This path should be: account_path +
        // 0x34044c6a65488ba0051b7669dae97b8b1fe0cdbb72351b0ca7b4dc42f50dd9b8
        let overlay_storage_nibbles = Nibbles::from_nibbles([
            0x3, 0x4, 0x0, 0x4, 0x4, 0xc, 0x6, 0xa, 0x6, 0x5, 0x4, 0x8, 0x8, 0xb, 0xa, 0x0, 0x0,
            0x5, 0x1, 0xb, 0x7, 0x6, 0x6, 0x9, 0xd, 0xa, 0xe, 0x9, 0x7, 0xb, 0x8, 0xb, 0x1, 0xf,
            0xe, 0x0, 0xc, 0xd, 0xb, 0xb, 0x7, 0x2, 0x3, 0x5, 0x1, 0xb, 0x0, 0xc, 0xa, 0x7, 0xb,
            0x4, 0xd, 0xc, 0x4, 0x2, 0xf, 0x5, 0x0, 0xd, 0xd, 0x9, 0xb, 0x8,
        ]);
        let overlay_storage_path = crate::path::StoragePath::for_address_path_and_slot_hash(
            account_path.clone(),
            overlay_storage_nibbles,
        );

        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut
            .insert(overlay_storage_path.full_path(), Some(OverlayValue::Storage(U256::from(999))));
        let overlay = overlay_mut.freeze();

        // This triggered a panic due to lexicographic ordering violation
        // The branch node at path ending in 0x340 will be added after its descendant
        // at path ending in 0x34044c6a65488ba0051b7669dae97b8b1fe0cdbb72351b0ca7b4dc42f50dd9b8
        let result = db.storage_engine.compute_root_with_overlay(&context, &overlay);
        let overlay_root = result.unwrap().0;

        // commit the overlay, ensure that the root is the same as the initial root
        let mut changes: Vec<(Nibbles, Option<TrieValue>)> = overlay
            .data()
            .iter()
            .map(|(path, value)| (path.clone(), value.clone().map(|v| v.try_into().unwrap())))
            .collect();
        db.storage_engine.set_values(&mut context, &mut changes).unwrap();
        let committed_root = context.root_node_hash;
        assert_eq!(committed_root, overlay_root);
    }

    #[test]
    fn test_complex_case() {}

    // #[test]
    // fn test_overlay_state_root_fuzz_rounds() {
    //     use crate::{path::AddressPath, path::StoragePath, Database};
    //     use alloy_primitives::{Address, B256, U256};
    //     use rand::{rngs::StdRng, Rng, SeedableRng};
    //     use std::collections::{HashMap, HashSet};
    //     use tempfile::TempDir;

    //     // Deterministic RNG for reproducibility
    //     let mut rng = StdRng::seed_from_u64(0xDEADBEEFCAFEBABE);

    //     // Create an empty DB
    //     let tmp_dir = TempDir::new().unwrap();
    //     let file_path = tmp_dir.path().join("test.db");
    //     let db = Database::create_new(file_path).unwrap();
    //     let mut context = db.storage_engine.write_context();

    //     // In-memory expected state: AddressPath -> (Account, slot_hash -> value)
    //     let mut state: HashMap<AddressPath, (Account, HashMap<B256, U256>)> = HashMap::new();
    //     let mut all_paths: Vec<AddressPath> = Vec::new();
    //     let mut used_paths: HashSet<AddressPath> = HashSet::new();

    //     // Pre-seed 10,000 accounts
    //     let mut initial_changes: Vec<(Nibbles, Option<TrieValue>)> = Vec::with_capacity(10_000);
    //     for i in 0..10_000u64 {
    //         let addr = Address::random();
    //         let ap = AddressPath::for_address(addr);
    //         used_paths.insert(ap.clone());
    //         all_paths.push(ap.clone());
    //         let account = Account::new(i, U256::from(rng.random::<u64>()), EMPTY_ROOT_HASH,
    // KECCAK_EMPTY);         state.insert(ap.clone(), (account.clone(), HashMap::new()));
    //         initial_changes.push((ap.into(), Some(TrieValue::Account(account))));
    //     }

    //     // Of these, 1,000 should have storage: 100 with 10 slots, 900 with 1,000 slots
    //     let storage_accounts_small: Vec<AddressPath> =
    // all_paths.iter().cloned().take(100).collect();     let storage_accounts_large:
    // Vec<AddressPath> = all_paths.iter().cloned().skip(100).take(900).collect();

    //     // Helper to insert unique slots for an address
    //     let mut insert_slots = |ap: &AddressPath, num_slots: usize| {
    //         let (_, ref mut slots) = state.get_mut(ap).unwrap();
    //         for _ in 0..num_slots {
    //             // Ensure unique slot per account
    //             let mut key: B256;
    //             loop {
    //                 key = B256::from(rng.random::<[u8; 32]>());
    //                 if !slots.contains_key(&key) {
    //                     break;
    //                 }
    //             }
    //             let value = U256::from(rng.random::<u128>());
    //             slots.insert(key, value);
    //             let storage_path = StoragePath::for_address_path_and_slot(ap.clone(), key);
    //             initial_changes.push((storage_path.full_path(),
    // Some(TrieValue::Storage(value))));         }
    //     };

    //     for ap in storage_accounts_small.iter() {
    //         insert_slots(ap, 10);
    //     }
    //     for ap in storage_accounts_large.iter() {
    //         insert_slots(ap, 1_000);
    //     }

    //     // Sort and commit initial state
    //     initial_changes.sort_by(|a, b| a.0.cmp(&b.0));
    //     db.storage_engine.set_values(&mut context, &mut initial_changes).unwrap();

    //     // Accounts considered to have storage (non-empty map)
    //     let mut accounts_with_storage: Vec<AddressPath> = state
    //         .iter()
    //         .filter_map(|(ap, (_acc, slots))| if !slots.is_empty() { Some(ap.clone()) } else {
    // None })         .collect();

    //     // Helper to sample n unique elements from a candidate list without replacement
    //     let mut sample_n = |cands_len: usize, n: usize| -> Vec<usize> {
    //         let n = n.min(cands_len);
    //         let mut idxs: Vec<usize> = (0..cands_len).collect();
    //         for i in 0..n {
    //             let rand_u = rng.random::<u64>() as usize;
    //             let j = i + (rand_u % (cands_len - i));
    //             idxs.swap(i, j);
    //         }
    //         idxs.truncate(n);
    //         idxs
    //     };

    //     // 100 rounds of randomized operations
    //     for _round in 0..100 {
    //         let mut overlay_mut = OverlayStateMut::new();

    //         // Insert 50 new accounts
    //         let mut new_accounts: Vec<AddressPath> = Vec::with_capacity(50);
    //         for i in 0..50u64 {
    //             let ap = loop {
    //                 let a = Address::random();
    //                 let candidate = AddressPath::for_address(a);
    //                 if !used_paths.contains(&candidate) {
    //                     break candidate;
    //                 }
    //             };
    //             used_paths.insert(ap.clone());
    //             new_accounts.push(ap.clone());
    //             all_paths.push(ap.clone());
    //             let account = Account::new(i, U256::from(rng.random::<u64>()), EMPTY_ROOT_HASH,
    // KECCAK_EMPTY);             state.insert(ap.clone(), (account.clone(), HashMap::new()));
    //             overlay_mut.insert(ap.into(), Some(OverlayValue::Account(account)));
    //         }

    //         // Update 50 existing accounts
    //         let existing_paths: Vec<AddressPath> = state.keys().cloned().collect();
    //         let filtered: Vec<AddressPath> = existing_paths
    //             .into_iter()
    //             .filter(|a| !new_accounts.contains(a))
    //             .collect();
    //         let idxs = sample_n(filtered.len(), 50);
    //         let update_targets: Vec<AddressPath> = idxs.into_iter().map(|i|
    // filtered[i].clone()).collect();         for ap in update_targets.iter().cloned() {
    //             if let Some((acc, _)) = state.get_mut(&ap) {
    //                 acc.balance = U256::from(rng.random::<u128>());
    //                 acc.nonce = acc.nonce.wrapping_add(1);
    //                 overlay_mut.insert(ap.into(), Some(OverlayValue::Account(acc.clone())));
    //             }
    //         }

    //         // Delete 10 accounts (avoid newly inserted and updated to keep sets disjoint)
    //         let delete_candidates: Vec<AddressPath> = state
    //             .keys()
    //             .filter(|a| !new_accounts.contains(a) && !update_targets.contains(a))
    //             .cloned()
    //             .collect();
    //         let idxs = sample_n(delete_candidates.len(), 10);
    //         let delete_targets: Vec<AddressPath> = idxs.into_iter().map(|i|
    // delete_candidates[i].clone()).collect();         for ap in delete_targets.iter().cloned()
    // {             overlay_mut.insert(ap.clone().into(), None);
    //             state.remove(&ap);
    //             accounts_with_storage.retain(|a| *a != ap);
    //         }

    //         // Storage operations
    //         // Helper: sample N accounts with at least K storage slots
    //         let mut sample_accounts_with_min_slots = |n: usize, k: usize| -> Vec<AddressPath> {
    //             let candidates: Vec<AddressPath> = accounts_with_storage
    //                 .iter()
    //                 .filter(|ap| state.get(*ap).map(|(_, m)| m.len()).unwrap_or(0) >= k)
    //                 .cloned()
    //                 .collect();
    //             let idxs = sample_n(candidates.len(), n);
    //             idxs.into_iter().map(|i| candidates[i].clone()).collect()
    //         };

    //         // Insert 100 new slots into 10 random storage accounts
    //         let insert_slot_accounts = sample_accounts_with_min_slots(10, 0);
    //         for ap in insert_slot_accounts.iter().cloned() {
    //             if let Some((_, slots)) = state.get_mut(&ap) {
    //                 for _ in 0..100 {
    //                     let key = loop {
    //                         let k = B256::from(rng.random::<[u8; 32]>());
    //                         if !slots.contains_key(&k) {
    //                             break k;
    //                         }
    //                     };
    //                     let value = U256::from(rng.random::<u128>());
    //                     slots.insert(key, value);
    //                     let storage_path = StoragePath::for_address_path_and_slot(ap.clone(),
    // key);                     overlay_mut.insert(storage_path.full_path(),
    // Some(OverlayValue::Storage(value)));                 }
    //                 if !accounts_with_storage.contains(&ap) {
    //                     accounts_with_storage.push(ap);
    //                 }
    //             }
    //         }

    //         // Update 10 slots in 10 random storage accounts (10 slots each)
    //         let update_slot_accounts = sample_accounts_with_min_slots(10, 10);
    //         for ap in update_slot_accounts.iter().cloned() {
    //             if let Some((_, map)) = state.get_mut(&ap) {
    //                 let keys: Vec<B256> = map.keys().cloned().collect();
    //                 let idxs = sample_n(keys.len(), 10);
    //                 for i in idxs {
    //                     let key = keys[i];
    //                     let new_value = U256::from(rng.random::<u128>());
    //                     map.insert(key, new_value);
    //                     let storage_path = StoragePath::for_address_path_and_slot(ap.clone(),
    // key);                     overlay_mut
    //                         .insert(storage_path.full_path(),
    // Some(OverlayValue::Storage(new_value)));                 }
    //             }
    //         }

    //         // Delete 10 slots in 10 random storage accounts (10 slots each)
    //         let delete_slot_accounts = sample_accounts_with_min_slots(10, 10);
    //         for ap in delete_slot_accounts.iter().cloned() {
    //             if let Some((_, map)) = state.get_mut(&ap) {
    //                 let keys: Vec<B256> = map.keys().cloned().collect();
    //                 let idxs = sample_n(keys.len(), 10);
    //                 for i in idxs {
    //                     let key = keys[i];
    //                     map.remove(&key);
    //                     let storage_path = StoragePath::for_address_path_and_slot(ap.clone(),
    // key);                     overlay_mut.insert(storage_path.full_path(), None);
    //                 }
    //                 if map.is_empty() {
    //                     accounts_with_storage.retain(|a| *a != ap);
    //                 }
    //             }
    //         }

    //         // Compute overlay root, apply, and compare
    //         let overlay = overlay_mut.freeze();
    //         let (overlay_root, _, _) = db.storage_engine.compute_root_with_overlay(&context,
    // &overlay).unwrap();

    //         let mut commit_changes: Vec<(Nibbles, Option<TrieValue>)> = overlay
    //             .data()
    //             .iter()
    //             .map(|(path, value)| (path.clone(), value.clone().map(|v|
    // v.try_into().unwrap())))             .collect();
    //         db.storage_engine.set_values(&mut context, &mut commit_changes).unwrap();
    //         let committed_root = context.root_node_hash;

    //         assert_eq!(overlay_root, committed_root);
    //     }
    // }
}
