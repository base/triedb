use std::rc::Rc;

use crate::{
    account::Account,
    context::TransactionContext,
    node::{encode_account_leaf, Node, NodeKind},
    overlay::{OverlayState, OverlayValue},
    page::SlottedPage,
    path::RawPath,
    pointer::Pointer,
    storage::engine::{Error, StorageEngine},
};
use alloy_primitives::{
    map::{B256Map, HashMap},
    B256, U256,
};
use alloy_rlp::encode_fixed_size;
use alloy_trie::{BranchNodeCompact, HashBuilder, Nibbles, EMPTY_ROOT_HASH};
use arrayvec::ArrayVec;

#[derive(Debug)]
enum TriePosition<'a> {
    Node(RawPath, Rc<SlottedPage<'a>>, Node),
    Pointer(RawPath, Rc<SlottedPage<'a>>, Pointer, bool),
    None,
}

struct TraversalStack<'a> {
    stack: Vec<(TriePosition<'a>, OverlayState)>,
}

impl<'a> TraversalStack<'a> {
    fn new() -> Self {
        Self { stack: vec![] }
    }

    fn push_node(
        &mut self,
        path: RawPath,
        node: Node,
        page: Rc<SlottedPage<'a>>,
        overlay: OverlayState,
    ) {
        self.push(TriePosition::Node(path, page, node), overlay);
    }

    fn push_pointer(
        &mut self,
        path: RawPath,
        pointer: Pointer,
        page: Rc<SlottedPage<'a>>,
        can_add_by_hash: bool,
        overlay: OverlayState,
    ) {
        self.push(TriePosition::Pointer(path, page, pointer, can_add_by_hash), overlay);
    }

    fn push_overlay(&mut self, overlay: OverlayState) {
        self.push(TriePosition::None, overlay);
    }

    fn push(&mut self, position: TriePosition<'a>, overlay: OverlayState) {
        self.stack.push((position, overlay));
    }

    fn pop(&mut self) -> Option<(TriePosition<'a>, OverlayState)> {
        self.stack.pop()
    }
}

#[derive(Debug)]
pub struct OverlayedRoot {
    pub root: B256,
    pub updated_branch_nodes: HashMap<Nibbles, BranchNodeCompact>,
    pub storage_branch_updates: B256Map<HashMap<Nibbles, BranchNodeCompact>>,
}

impl OverlayedRoot {
    pub fn new(
        root: B256,
        updated_branch_nodes: HashMap<Nibbles, BranchNodeCompact>,
        storage_branch_updates: B256Map<HashMap<Nibbles, BranchNodeCompact>>,
    ) -> Self {
        Self { root, updated_branch_nodes, storage_branch_updates }
    }

    pub fn new_hash(root: B256) -> Self {
        Self {
            root,
            updated_branch_nodes: HashMap::default(),
            storage_branch_updates: B256Map::default(),
        }
    }
}
struct RootBuilder {
    hash_builder: HashBuilder,
    storage_branch_updates: B256Map<HashMap<Nibbles, BranchNodeCompact>>,
}

impl RootBuilder {
    fn new() -> Self {
        Self {
            hash_builder: HashBuilder::default().with_updates(true),
            storage_branch_updates: B256Map::default(),
        }
    }

    fn add_leaf(&mut self, key: Nibbles, value: &[u8]) {
        self.hash_builder.add_leaf(key, value);
    }

    fn add_branch(&mut self, key: Nibbles, value: B256, stored_in_database: bool) {
        self.hash_builder.add_branch(key, value, stored_in_database);
    }

    fn add_storage_branch_updates(
        &mut self,
        account: B256,
        updates: HashMap<Nibbles, BranchNodeCompact>,
    ) {
        self.storage_branch_updates.insert(account, updates);
    }

    fn finalize(self) -> OverlayedRoot {
        let (mut hash_builder, updated_branch_nodes) = self.hash_builder.split();
        OverlayedRoot::new(hash_builder.root(), updated_branch_nodes, self.storage_branch_updates)
    }
}

impl StorageEngine {
    pub fn compute_state_root_with_overlay(
        &self,
        context: &TransactionContext,
        overlay: OverlayState,
    ) -> Result<OverlayedRoot, Error> {
        if overlay.is_empty() {
            return Ok(OverlayedRoot::new_hash(context.root_node_hash));
        }

        let mut root_builder = RootBuilder::new();

        let root_page = if let Some(root_page_id) = context.root_node_page_id {
            let page = self.get_page(context, root_page_id)?;
            SlottedPage::try_from(page).unwrap()
        } else {
            self.add_overlay_to_root_builder(&mut root_builder, &overlay);
            return Ok(root_builder.finalize());
        };

        let root_node: Node = root_page.get_value(0)?;
        let mut stack = TraversalStack::new();
        stack.push_node(root_node.prefix().into(), root_node, Rc::new(root_page), overlay);

        self.compute_root_with_overlay(context, &mut stack, &mut root_builder)?;

        Ok(root_builder.finalize())
    }

    fn compute_root_with_overlay<'a>(
        &'a self,
        context: &TransactionContext,
        stack: &mut TraversalStack<'a>,
        root_builder: &mut RootBuilder,
    ) -> Result<(), Error> {
        // Depth first traversal of the trie, starting at the root node.
        // This applies any overlay state to the trie, taking precedence over the trie's own values.
        // Whenever a branch or leaf is known to be the final unchanged value, we can add it to the
        // hash builder.
        while let Some((position, overlay)) = stack.pop() {
            match position {
                TriePosition::None => {
                    // No trie position, process whatever is in the overlay
                    self.add_overlay_to_root_builder(root_builder, &overlay);
                }
                TriePosition::Pointer(path, page, pointer, can_add_by_hash) => {
                    if overlay.is_empty() && can_add_by_hash {
                        if let Some(hash) = pointer.rlp().as_hash() {
                            // No overlay, just add the pointer by hash
                            root_builder.add_branch(path.try_into().unwrap(), hash, true);
                            continue;
                        }
                    }
                    // We have an overlay, need to process the child
                    self.process_overlayed_child(
                        context,
                        overlay,
                        root_builder,
                        path,
                        &pointer,
                        page,
                        stack,
                    )?;
                }
                TriePosition::Node(path, page, node) => {
                    let (pre_overlay, matching_overlay, post_overlay) =
                        overlay.sub_slice_by_prefix(&path);
                    if pre_overlay.contains_prefix_of(&path) {
                        // The pre_overlay invalidates the current node, so we can simply add the
                        // full overlay. We need to process it all together,
                        // as the post_overlay may contain descendants of the pre_overlay.
                        self.add_overlay_to_root_builder(root_builder, &overlay);
                        continue;
                    }

                    self.add_overlay_to_root_builder(root_builder, &pre_overlay);
                    // Defer the post_overlay to be processed after the node is traversed
                    stack.push_overlay(post_overlay);

                    match node.into_kind() {
                        NodeKind::Branch { children } => {
                            if let Some((overlay_path, Some(OverlayValue::Hash(_)))) =
                                matching_overlay.first()
                            {
                                if overlay_path == path {
                                    // the overlay invalidates the current node, so just add this
                                    // and skip the rest of the db traversal
                                    self.add_overlay_to_root_builder(
                                        root_builder,
                                        &matching_overlay,
                                    );
                                    continue;
                                }
                            }
                            self.process_branch_node_with_overlay(
                                matching_overlay,
                                &path,
                                children,
                                page,
                                stack,
                            )?;
                        }
                        NodeKind::AccountLeaf {
                            nonce_rlp,
                            balance_rlp,
                            code_hash,
                            storage_root,
                        } => {
                            self.process_account_leaf_with_overlay(
                                context,
                                &matching_overlay,
                                root_builder,
                                &path,
                                page,
                                nonce_rlp,
                                balance_rlp,
                                code_hash,
                                storage_root,
                            )?;
                        }
                        NodeKind::StorageLeaf { value_rlp } => {
                            if let Some((overlay_path, _)) = matching_overlay.first() {
                                if overlay_path == path {
                                    // the overlay invalidates the current node, so just add this
                                    // and skip the rest of the db traversal
                                    self.add_overlay_to_root_builder(
                                        root_builder,
                                        &matching_overlay,
                                    );
                                    continue;
                                }
                            }
                            // Leaf node, add it to the hash builder
                            root_builder.add_leaf(path.try_into().unwrap(), &value_rlp);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn process_branch_node_with_overlay<'a>(
        &'a self,
        mut overlay: OverlayState,
        path: &RawPath,
        mut children: [Option<Pointer>; 16],
        current_page: Rc<SlottedPage<'a>>,
        stack: &mut TraversalStack<'a>,
    ) -> Result<(), Error> {
        let mut child_data = ArrayVec::<_, 16>::new();

        let mut minimum_possible_child_count = 0;
        for idx in 0..16 {
            let child_pointer = children[idx as usize].take();
            if child_pointer.is_none() && overlay.is_empty() {
                continue;
            }

            let mut child_path = *path;
            child_path.push(idx);
            let (_, child_overlay, overlay_after_child) = overlay.sub_slice_by_prefix(&child_path);

            if child_pointer.is_some() && child_overlay.is_empty() {
                minimum_possible_child_count += 1;
            } else if let Some((_, Some(_))) = child_overlay.first() {
                // we have a non-tombstone overlay, so there must be at least one descendant
                // in this child index
                minimum_possible_child_count += 1;
            }

            child_data.push((child_path, child_pointer, child_overlay));
            overlay = overlay_after_child;
        }
        let can_add_by_hash = minimum_possible_child_count > 1;

        for (child_path, child_pointer, child_overlay) in child_data.into_iter().rev() {
            match child_pointer {
                Some(pointer) => {
                    stack.push_pointer(
                        child_path,
                        pointer,
                        current_page.clone(),
                        can_add_by_hash,
                        child_overlay,
                    );
                }
                None => {
                    if child_overlay.is_empty() {
                        // nothing here to add
                    } else {
                        // we have a nonconflicting overlay, add all of it to the hash builder
                        stack.push_overlay(child_overlay);
                    }
                }
            }
        }
        Ok(())
    }

    fn process_account_leaf_with_overlay<'a>(
        &'a self,
        context: &TransactionContext,
        overlay: &OverlayState,
        root_builder: &mut RootBuilder,
        path: &RawPath,
        current_page: Rc<SlottedPage<'a>>,
        mut nonce_rlp: ArrayVec<u8, 9>,
        mut balance_rlp: ArrayVec<u8, 33>,
        mut code_hash: B256,
        storage_root: Option<Pointer>,
    ) -> Result<(), Error> {
        let overlayed_account = overlay.lookup(path);
        match overlayed_account {
            Some(None) => {
                // The account is removed in the overlay
                return Ok(());
            }
            Some(Some(OverlayValue::Account(overlayed_account))) => {
                // The account is updated in the overlay
                nonce_rlp = alloy_rlp::encode_fixed_size(&overlayed_account.nonce);
                balance_rlp = alloy_rlp::encode_fixed_size(&overlayed_account.balance);
                code_hash = overlayed_account.code_hash;
            }
            _ => {
                // The account is not updated in the overlay
            }
        };

        let has_storage_overlays = overlay.iter().any(|(path, _)| path.len() > 64);
        if !has_storage_overlays {
            let storage_root_hash = storage_root
                .as_ref()
                .map_or(EMPTY_ROOT_HASH, |p| p.rlp().as_hash().unwrap_or(EMPTY_ROOT_HASH));

            self.add_account_leaf_to_root_builder(
                root_builder,
                *path,
                &nonce_rlp,
                &balance_rlp,
                &code_hash,
                &storage_root_hash,
            );
            return Ok(());
        }

        let mut storage_root_builder = RootBuilder::new();

        // We have storage overlays, need to compute a new storage root
        let storage_overlay = overlay.with_prefix_offset(64);

        match storage_root {
            Some(pointer) => {
                let mut storage_stack = TraversalStack::new();

                // load the root storage node
                if let Some(child_cell) = pointer.location().cell_index() {
                    let root_storage_node: Node = current_page.get_value(child_cell)?;
                    storage_stack.push_node(
                        root_storage_node.prefix().into(),
                        root_storage_node,
                        current_page,
                        storage_overlay,
                    );
                    self.compute_root_with_overlay(
                        context,
                        &mut storage_stack,
                        &mut storage_root_builder,
                    )?
                } else {
                    let storage_page =
                        self.get_page(context, pointer.location().page_id().unwrap())?;
                    let slotted_page = SlottedPage::try_from(storage_page)?;
                    let root_storage_node: Node = slotted_page.get_value(0)?;
                    storage_stack.push_node(
                        root_storage_node.prefix().into(),
                        root_storage_node,
                        Rc::new(slotted_page),
                        storage_overlay,
                    );
                    self.compute_root_with_overlay(
                        context,
                        &mut storage_stack,
                        &mut storage_root_builder,
                    )?;
                }
            }
            None => {
                // No existing storage root, just add the overlay
                self.add_overlay_to_root_builder(&mut storage_root_builder, &storage_overlay);
            }
        };
        let (mut storage_hash_builder, updated_storage_branch_nodes) =
            storage_root_builder.hash_builder.split();
        let new_root = storage_hash_builder.root();

        root_builder.add_storage_branch_updates(
            B256::from_slice(&path.pack::<32>()),
            updated_storage_branch_nodes,
        );

        self.add_account_leaf_to_root_builder(
            root_builder,
            *path,
            &nonce_rlp,
            &balance_rlp,
            &code_hash,
            &new_root,
        );

        Ok(())
    }

    fn add_account_leaf_to_root_builder(
        &self,
        root_builder: &mut RootBuilder,
        path: RawPath,
        nonce_rlp: &ArrayVec<u8, 9>,
        balance_rlp: &ArrayVec<u8, 33>,
        code_hash: &B256,
        storage_root: &B256,
    ) {
        let mut buf = [0u8; 110]; // max RLP length for an account: 2 bytes for list length, 9 for nonce, 33 for
                                  // balance, 33 for storage root, 33 for code hash
        let mut value_rlp = buf.as_mut();
        let account_rlp_length =
            encode_account_leaf(nonce_rlp, balance_rlp, code_hash, storage_root, &mut value_rlp);
        root_builder.add_leaf(path.try_into().unwrap(), &buf[..account_rlp_length]);
    }

    fn process_overlayed_child<'a>(
        &'a self,
        context: &TransactionContext,
        overlay: OverlayState,
        root_builder: &mut RootBuilder,
        mut child_path: RawPath,
        child: &Pointer,
        current_page: Rc<SlottedPage<'a>>,
        stack: &mut TraversalStack<'a>,
    ) -> Result<(), Error> {
        // First consider the overlay. All values in it must already contain the child_path prefix.
        // If the overlay matches the child path, we can add it to the hash builder and skip
        // actually reading the child node.
        // Account values cannot be directly overlayed, as they may need to be merged with the
        // existing storage trie.
        if let Some((overlay_path, overlay_value)) = overlay.first() {
            if child_path == overlay_path &&
                !matches!(overlay_value, Some(OverlayValue::Account(_)))
            {
                // the child path is directly overlayed, so only use the overlay state
                self.add_overlay_to_root_builder(root_builder, &overlay);
                return Ok(());
            }
        }

        if let Some(child_cell) = child.location().cell_index() {
            let child_node: Node = current_page.get_value(child_cell)?;
            child_path.extend(&child_node.prefix().into());
            stack.push_node(child_path, child_node, current_page, overlay);
        } else {
            let child_page_id = child.location().page_id().unwrap();
            let child_page = self.get_page(context, child_page_id)?;
            let child_slotted_page = SlottedPage::try_from(child_page).unwrap();
            let child_node: Node = child_slotted_page.get_value(0)?;
            child_path.extend(&child_node.prefix().into());
            stack.push_node(child_path, child_node, Rc::new(child_slotted_page), overlay);
        }
        Ok(())
    }

    fn process_overlayed_account(
        &self,
        root_builder: &mut RootBuilder,
        path: Nibbles,
        account: &Account,
        storage_overlay: OverlayState,
    ) -> Result<(), Error> {
        if storage_overlay.is_empty() {
            let encoded = self.encode_account(account);
            root_builder.add_leaf(path, &encoded);
            return Ok(());
        }

        let mut storage_root_builder = RootBuilder::new();
        self.add_overlay_to_root_builder(&mut storage_root_builder, &storage_overlay);

        let (mut storage_hash_builder, updated_storage_branch_nodes) =
            storage_root_builder.hash_builder.split();
        let storage_root = storage_hash_builder.root();

        root_builder.add_storage_branch_updates(
            B256::from_slice(&path.pack()),
            updated_storage_branch_nodes,
        );

        let encoded = self.encode_account_with_root(account, storage_root);
        root_builder.add_leaf(path, &encoded);
        Ok(())
    }

    fn add_overlay_to_root_builder(&self, root_builder: &mut RootBuilder, overlay: &OverlayState) {
        let mut last_processed_path = None;
        for (path, value) in overlay.iter() {
            if let Some(last_processed_path) = last_processed_path {
                if path.starts_with(&last_processed_path) {
                    // skip over all descendants of a processed path
                    continue;
                }
            }

            match value {
                Some(OverlayValue::Account(account)) => {
                    let storage_overlay =
                        overlay.sub_slice_for_prefix(&path).with_prefix_offset(64);
                    self.process_overlayed_account(
                        root_builder,
                        path.try_into().unwrap(),
                        account,
                        storage_overlay,
                    )
                    .unwrap();
                    last_processed_path = Some(path);
                }
                Some(OverlayValue::Storage(storage_value)) => {
                    let encoded = self.encode_storage(storage_value);
                    root_builder.add_leaf(path.try_into().unwrap(), &encoded);
                }
                Some(OverlayValue::Hash(hash)) => {
                    root_builder.add_branch(path.try_into().unwrap(), *hash, false);
                    last_processed_path = Some(path);
                }
                None => {
                    // Tombstone - skip
                    last_processed_path = Some(path);
                }
            }
        }
    }

    #[inline]
    pub fn encode_account(&self, account: &Account) -> ArrayVec<u8, 110> {
        let trie_account = Account {
            nonce: account.nonce,
            balance: account.balance,
            storage_root: account.storage_root,
            code_hash: account.code_hash,
        };
        encode_fixed_size(&trie_account)
    }

    #[inline]
    pub fn encode_account_with_root(&self, account: &Account, root: B256) -> ArrayVec<u8, 110> {
        let trie_account = Account {
            nonce: account.nonce,
            balance: account.balance,
            storage_root: root,
            code_hash: account.code_hash,
        };
        encode_fixed_size(&trie_account)
    }

    #[inline]
    pub fn encode_storage(&self, storage_value: &U256) -> ArrayVec<u8, 33> {
        encode_fixed_size(storage_value)
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::{address, Address, U256};
    use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
    use rand::Rng;
    use tempdir::TempDir;

    use crate::{
        account::Account,
        database::Database,
        node::TrieValue,
        overlay::{OverlayStateMut, OverlayValue},
        path::{AddressPath, StoragePath},
    };

    use super::*;

    fn compare_overlay_with_committed_root(
        db: &Database,
        context: &mut TransactionContext,
        overlay: &OverlayState,
    ) -> B256 {
        let initial_root = context.root_node_hash;
        let output =
            db.storage_engine.compute_state_root_with_overlay(context, overlay.clone()).unwrap();
        let (overlay_root, account_branch_updates, storage_branch_updates) =
            (output.root, output.updated_branch_nodes, output.storage_branch_updates);
        assert_ne!(overlay_root, initial_root, "Overlay should not match initial root");

        let mut overlay_mut_with_branches = OverlayStateMut::new();

        overlay.data().iter().for_each(|(path, value)| {
            overlay_mut_with_branches.insert(*path, value.clone());
        });

        for (path, branch) in account_branch_updates.into_iter() {
            if let Some(root_hash) = branch.root_hash {
                overlay_mut_with_branches.insert(path.into(), Some(OverlayValue::Hash(root_hash)));
            }
            let mut hash_idx = 0;
            let mut path = path;
            for i in 0..16 {
                if branch.hash_mask.is_bit_set(i) {
                    path.push(i);
                    overlay_mut_with_branches
                        .insert(path.into(), Some(OverlayValue::Hash(branch.hashes[hash_idx])));
                    hash_idx += 1;
                    path.pop();
                }
            }
        }

        for (account, branches) in storage_branch_updates.iter() {
            for (path, branch) in branches.iter() {
                if let Some(root_hash) = branch.root_hash {
                    overlay_mut_with_branches.insert(
                        RawPath::unpack(account.as_ref()).join(&path.into()),
                        Some(OverlayValue::Hash(root_hash)),
                    );
                }
                let mut hash_idx = 0;
                let mut path = *path;
                for i in 0..16 {
                    if branch.hash_mask.is_bit_set(i) {
                        path.push(i);
                        overlay_mut_with_branches.insert(
                            RawPath::unpack(account.as_ref()).join(&path.into()),
                            Some(OverlayValue::Hash(branch.hashes[hash_idx])),
                        );
                        hash_idx += 1;
                        path.pop();
                    }
                }
            }
        }

        let overlay_with_branches = overlay_mut_with_branches.freeze();

        let output = db
            .storage_engine
            .compute_state_root_with_overlay(context, overlay_with_branches.clone())
            .unwrap();
        let (overlay_root_with_branches, _, _) =
            (output.root, output.updated_branch_nodes, output.storage_branch_updates);
        assert_eq!(overlay_root_with_branches, overlay_root);

        let mut changes: Vec<(RawPath, Option<TrieValue>)> = overlay
            .data()
            .iter()
            .map(|(path, value)| (*path, value.clone().map(|v| v.try_into().unwrap())))
            .collect();
        db.storage_engine.set_values(context, &mut changes).unwrap();
        let committed_root = context.root_node_hash;
        assert_eq!(overlay_root, committed_root, "Overlay should match committed root");

        // recompute the root with overlayed state that is already committed. This should match the
        // committed root.
        let output = db
            .storage_engine
            .compute_state_root_with_overlay(context, overlay_with_branches)
            .unwrap();
        let (overlay_root_after_commit, _, _) =
            (output.root, output.updated_branch_nodes, output.storage_branch_updates);
        assert_eq!(overlay_root_after_commit, committed_root);

        overlay_root
    }

    #[test]
    fn test_empty_overlay_root() {
        let tmp_dir = TempDir::new("test_overlay_root_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let context = db.storage_engine.read_context();
        let empty_overlay = OverlayStateMut::new().freeze();

        let output =
            db.storage_engine.compute_state_root_with_overlay(&context, empty_overlay).unwrap();
        assert_eq!(output.root, context.root_node_hash);
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
        let output = db.storage_engine.compute_state_root_with_overlay(&context, overlay).unwrap();

        // The root should be different from the empty root (since we have changes)
        assert_ne!(output.root, EMPTY_ROOT_HASH);
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

        // Now test with actual overlay changes - modify the same account with different values
        let mut overlay_mut = OverlayStateMut::new();
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        overlay_mut
            .insert(address_path.clone().into(), Some(OverlayValue::Account(account2.clone())));
        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
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

        compare_overlay_with_committed_root(&db, &mut context, &overlay);

        // Test Case 2: Overlay that creates a new account in an empty subtree (None child case),
        // affects an existing subtree, and leaves one unaffected Path 3: starts with 0x2...
        // (first nibble = 2) - this child doesn't exist on disk
        let path3 = AddressPath::new(Nibbles::from_nibbles([
            0x2, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        ]));

        let account3 = Account::new(3, U256::from(300), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let mut overlay_mut2 = OverlayStateMut::new();
        overlay_mut2.insert(path1.clone().into(), Some(OverlayValue::Account(account3.clone())));
        overlay_mut2.insert(path3.clone().into(), Some(OverlayValue::Account(account3.clone())));
        let overlay2 = overlay_mut2.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay2);
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

        let overlay_root = compare_overlay_with_committed_root(&db, &mut context, &overlay);

        assert_eq!(
            overlay_root, root_without_account2,
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
        let account_path = RawPath::from(AddressPath::for_address(account_address));
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // Create storage paths for the account
        let storage_key1 = U256::from(42);
        let storage_key2 = U256::from(99);
        let storage_path1 =
            RawPath::from(StoragePath::for_address_and_slot(account_address, storage_key1.into()));
        let storage_path2 =
            RawPath::from(StoragePath::for_address_and_slot(account_address, storage_key2.into()));

        let storage_value1 = U256::from(123);
        let storage_value2 = U256::from(456);

        // Set up initial state with account and storage
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path, Some(TrieValue::Account(account.clone()))),
                    (storage_path1, Some(TrieValue::Storage(storage_value1))),
                    (storage_path2, Some(TrieValue::Storage(storage_value2))),
                ],
            )
            .unwrap();

        // Test Case 1: Overlay that modifies existing storage
        let mut overlay_mut = OverlayStateMut::new();
        let new_storage_value1 = U256::from(999);
        overlay_mut.insert(storage_path1, Some(OverlayValue::Storage(new_storage_value1)));
        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);

        // Test Case 2: Overlay that adds new storage
        let mut overlay_mut2 = OverlayStateMut::new();
        let storage_key3 = U256::from(200);
        let storage_path3 =
            RawPath::from(StoragePath::for_address_and_slot(account_address, storage_key3.into()));
        let storage_value3 = U256::from(789);
        overlay_mut2.insert(storage_path3, Some(OverlayValue::Storage(storage_value3)));
        let overlay2 = overlay_mut2.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay2);

        // Test Case 3: Overlay that deletes storage (tombstone)
        let mut overlay_mut3 = OverlayStateMut::new();
        overlay_mut3.insert(storage_path2, None); // Delete storage slot
        let overlay3 = overlay_mut3.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay3);

        // Test Case 4: Combined account and storage changes
        let mut overlay_mut4 = OverlayStateMut::new();
        let updated_account = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        overlay_mut4.insert(account_path, Some(OverlayValue::Account(updated_account.clone())));
        overlay_mut4.insert(storage_path1, Some(OverlayValue::Storage(new_storage_value1)));
        let overlay4 = overlay_mut4.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay4);

        // Test Case 5: Overlay that deletes storage slot via a zero value
        let mut overlay_mut5 = OverlayStateMut::new();
        overlay_mut5.insert(storage_path1, Some(OverlayValue::Storage(U256::ZERO)));
        let overlay5 = overlay_mut5.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay5);
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
        let storage_path1 = StoragePath::for_address_and_slot(account_address, storage_key1.into());

        // Set up initial state with 1 storage slot
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path.into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.into(), Some(TrieValue::Storage(U256::from(111)))),
                ],
            )
            .unwrap();

        // Test: Add a NEW storage slot via overlay
        let mut overlay_mut = OverlayStateMut::new();
        let storage_key2 = U256::from(20); // New storage key
        let storage_path2 = StoragePath::for_address_and_slot(account_address, storage_key2.into());

        overlay_mut.insert(storage_path2.into(), Some(OverlayValue::Storage(U256::from(222))));
        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
    }

    #[test]
    fn test_overlay_account_with_storage() {
        let tmp_dir = TempDir::new("test_overlay_account_with_storage_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create an account with some storage
        let account_address = address!("0x0000000000000000000000000000000000000001");
        let account_path = RawPath::from(AddressPath::for_address(account_address));
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let storage_key = U256::from(10);
        let storage_path =
            RawPath::from(StoragePath::for_address_and_slot(account_address, storage_key.into()));

        // Set up initial state with account and storage
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path, Some(TrieValue::Account(account.clone()))),
                    (storage_path, Some(TrieValue::Storage(U256::from(111)))),
                ],
            )
            .unwrap();

        // Test: Overlay that modifies the account value (but not the storage root)
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(
            account_path,
            Some(OverlayValue::Account(Account::new(
                2,
                U256::from(200),
                EMPTY_ROOT_HASH,
                KECCAK_EMPTY,
            ))),
        );
        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
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

        let account1_path = RawPath::from(AddressPath::for_address(account1_address));
        let account2_path = RawPath::from(AddressPath::for_address(account2_address));

        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // One storage slot for each account
        let storage1_key = U256::from(10);
        let storage2_key = U256::from(20);
        let storage1_path =
            RawPath::from(StoragePath::for_address_and_slot(account1_address, storage1_key.into()));
        let storage2_path =
            RawPath::from(StoragePath::for_address_and_slot(account2_address, storage2_key.into()));

        // Set up initial state
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account1_path, Some(TrieValue::Account(account1.clone()))),
                    (account2_path, Some(TrieValue::Account(account2.clone()))),
                    (storage1_path, Some(TrieValue::Storage(U256::from(111)))),
                    (storage2_path, Some(TrieValue::Storage(U256::from(222)))),
                ],
            )
            .unwrap();

        // Test: Modify just one storage value per account via overlay
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage1_path, Some(OverlayValue::Storage(U256::from(999))));
        overlay_mut.insert(storage2_path, Some(OverlayValue::Storage(U256::from(888))));
        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
    }

    #[test]
    fn test_debug_multiple_storage_overlays_same_account() {
        let tmp_dir = TempDir::new("test_debug_multiple_overlays_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create one account with 2 initial storage slots
        let account_address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account_path = RawPath::from(AddressPath::for_address(account_address));
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let storage_key1 = U256::from(10);
        let storage_key2 = U256::from(20);
        let storage_path1 =
            RawPath::from(StoragePath::for_address_and_slot(account_address, storage_key1.into()));
        let storage_path2 =
            RawPath::from(StoragePath::for_address_and_slot(account_address, storage_key2.into()));

        // Set up initial state
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path, Some(TrieValue::Account(account.clone()))),
                    (storage_path1, Some(TrieValue::Storage(U256::from(111)))),
                    (storage_path2, Some(TrieValue::Storage(U256::from(222)))),
                ],
            )
            .unwrap();

        // Test: Apply MULTIPLE storage overlays to the same account
        let mut overlay_mut = OverlayStateMut::new();

        // Modify existing storage slot 1
        overlay_mut.insert(storage_path1, Some(OverlayValue::Storage(U256::from(1111))));

        // Add new storage slot 3
        let storage_key3 = U256::from(40);
        let storage_path3 =
            RawPath::from(StoragePath::for_address_and_slot(account_address, storage_key3.into()));

        overlay_mut.insert(storage_path3, Some(OverlayValue::Storage(U256::from(444))));

        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
    }

    #[test]
    fn test_debug_overlay_vs_committed_single_account() {
        let tmp_dir = TempDir::new("test_debug_overlay_committed_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        // Create one account with 2 storage slots
        let account_address = address!("0x0000000000000000000000000000000000000001");
        let account_path = RawPath::from(AddressPath::for_address(account_address));
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let storage_key1 = U256::from(10);
        let storage_key2 = U256::from(20);
        let storage_path1 =
            RawPath::from(StoragePath::for_address_and_slot(account_address, storage_key1.into()));
        let storage_path2 =
            RawPath::from(StoragePath::for_address_and_slot(account_address, storage_key2.into()));

        // Set up initial state with 2 storage slots
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path, Some(TrieValue::Account(account.clone()))),
                    (storage_path1, Some(TrieValue::Storage(U256::from(111)))),
                    (storage_path2, Some(TrieValue::Storage(U256::from(222)))),
                ],
            )
            .unwrap();

        // Test: Overlay that modifies ONLY ONE storage slot, leaving the other unchanged
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage_path1, Some(OverlayValue::Storage(U256::from(999))));
        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
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

        let account1_path = RawPath::from(AddressPath::for_address(account1_address));
        let account2_path = RawPath::from(AddressPath::for_address(account2_address));

        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // Storage for account1
        let storage1_key1 = U256::from(10);
        let storage1_key2 = U256::from(20);
        let storage1_path1 = RawPath::from(StoragePath::for_address_and_slot(
            account1_address,
            storage1_key1.into(),
        ));
        let storage1_path2 = RawPath::from(StoragePath::for_address_and_slot(
            account1_address,
            storage1_key2.into(),
        ));

        // Storage for account2
        let storage2_key1 = U256::from(30);
        let storage2_path1 = RawPath::from(StoragePath::for_address_and_slot(
            account2_address,
            storage2_key1.into(),
        ));

        // Set up initial state
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account1_path, Some(TrieValue::Account(account1.clone()))),
                    (account2_path, Some(TrieValue::Account(account2.clone()))),
                    (storage1_path1, Some(TrieValue::Storage(U256::from(111)))),
                    (storage1_path2, Some(TrieValue::Storage(U256::from(222)))),
                    (storage2_path1, Some(TrieValue::Storage(U256::from(333)))),
                ],
            )
            .unwrap();

        // Test: Overlay changes to both accounts' storage
        let mut overlay_mut = OverlayStateMut::new();

        // Modify account1's storage
        overlay_mut.insert(storage1_path1, Some(OverlayValue::Storage(U256::from(1111))));

        // Add new storage to account1
        let storage1_key3 = U256::from(40);
        let storage1_path3 = RawPath::from(StoragePath::for_address_and_slot(
            account1_address,
            storage1_key3.into(),
        ));
        overlay_mut.insert(storage1_path3, Some(OverlayValue::Storage(U256::from(444))));

        // Modify account2's storage
        overlay_mut.insert(storage2_path1, Some(OverlayValue::Storage(U256::from(3333))));

        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
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

        let account1_path = RawPath::from(AddressPath::for_address(account1_address));
        let account2_path = RawPath::from(AddressPath::for_address(account2_address));

        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // One storage slot for each account
        let storage1_key = U256::from(10);
        let storage2_key = U256::from(20);
        let storage1_path =
            RawPath::from(StoragePath::for_address_and_slot(account1_address, storage1_key.into()));
        let storage2_path =
            RawPath::from(StoragePath::for_address_and_slot(account2_address, storage2_key.into()));

        // Set up initial state
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account1_path, Some(TrieValue::Account(account1.clone()))),
                    (account2_path, Some(TrieValue::Account(account2.clone()))),
                    (storage1_path, Some(TrieValue::Storage(U256::from(111)))),
                    (storage2_path, Some(TrieValue::Storage(U256::from(222)))),
                ],
            )
            .unwrap();

        // Test: Modify just one storage slot for account1
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage1_path, Some(OverlayValue::Storage(U256::from(999))));
        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
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

        let account1_path = RawPath::from(AddressPath::for_address(account1_address));
        let account2_path = RawPath::from(AddressPath::for_address(account2_address));

        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // One storage slot for each account
        let storage1_key = U256::from(10);
        let storage2_key = U256::from(20);
        let storage1_path =
            RawPath::from(StoragePath::for_address_and_slot(account1_address, storage1_key.into()));
        let storage2_path =
            RawPath::from(StoragePath::for_address_and_slot(account2_address, storage2_key.into()));

        // Set up initial state
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account1_path, Some(TrieValue::Account(account1.clone()))),
                    (account2_path, Some(TrieValue::Account(account2.clone()))),
                    (storage1_path, Some(TrieValue::Storage(U256::from(111)))),
                    (storage2_path, Some(TrieValue::Storage(U256::from(222)))),
                ],
            )
            .unwrap();

        // Test: Modify storage for BOTH accounts
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage1_path, Some(OverlayValue::Storage(U256::from(999))));
        overlay_mut.insert(storage2_path, Some(OverlayValue::Storage(U256::from(888))));
        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
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

        let account1_path = RawPath::from(AddressPath::for_address(account1_address));
        let account2_path = RawPath::from(AddressPath::for_address(account2_address));

        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        // Initial storage
        let storage1_key1 = U256::from(10);
        let storage1_path1 = RawPath::from(StoragePath::for_address_and_slot(
            account1_address,
            storage1_key1.into(),
        ));

        // Set up initial state with just one storage slot
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account1_path, Some(TrieValue::Account(account1.clone()))),
                    (account2_path, Some(TrieValue::Account(account2.clone()))),
                    (storage1_path1, Some(TrieValue::Storage(U256::from(111)))),
                ],
            )
            .unwrap();

        // Test: Add NEW storage to account1
        let mut overlay_mut = OverlayStateMut::new();
        let storage1_key2 = U256::from(40); // New storage key
        let storage1_path2 = RawPath::from(StoragePath::for_address_and_slot(
            account1_address,
            storage1_key2.into(),
        ));

        overlay_mut.insert(storage1_path2, Some(OverlayValue::Storage(U256::from(444))));
        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
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
                &mut [(account_path.into(), Some(TrieValue::Account(account.clone())))],
            )
            .unwrap();

        // Test: Add storage to account that had no storage before
        let mut overlay_mut = OverlayStateMut::new();
        let storage_key = U256::from(42);
        let storage_path = StoragePath::for_address_and_slot(account_address, storage_key.into());
        let storage_value = U256::from(123);
        overlay_mut.insert(storage_path.into(), Some(OverlayValue::Storage(storage_value)));
        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
    }

    #[test]
    fn test_1000_accounts_with_10_overlay() {
        for _ in 0..10 {
            let tmp_dir = TempDir::new("test_1000_accounts_with_10_overlay").unwrap();
            let file_path = tmp_dir.path().join("test.db");
            let db = Database::create_new(file_path).unwrap();

            let mut context = db.storage_engine.write_context();
            let mut rng = rand::rng();

            let mut changes: Vec<(RawPath, Option<TrieValue>)> = Vec::with_capacity(1000);

            for i in 0..1000 {
                let account_address = Address::random();
                let account =
                    Account::new(i, U256::from(rng.random::<u64>()), EMPTY_ROOT_HASH, KECCAK_EMPTY);
                let account_path = AddressPath::for_address(account_address);

                changes.push((account_path.into(), Some(TrieValue::Account(account))));
            }

            changes.sort_by(|a, b| a.0.cmp(&b.0));

            db.storage_engine.set_values(&mut context, &mut changes).unwrap();

            // Create overlay with modifications to every 100th account
            let mut overlay_mut = OverlayStateMut::new();

            // Take every 100th account from the changes
            for (i, (path, value)) in changes.iter().step_by(100).enumerate() {
                if let Some(TrieValue::Account(account)) = value {
                    if i % 2 == 0 {
                        // For half of the sampled accounts, create new modified account
                        let mut new_account = account.clone();
                        new_account.balance = U256::from(rng.random::<u64>()); // Random new balance
                        overlay_mut.insert(*path, Some(OverlayValue::Account(new_account)));
                    } else {
                        // For other half, mark for deletion
                        overlay_mut.insert(*path, None);
                    }
                }
            }
            let overlay = overlay_mut.freeze();

            compare_overlay_with_committed_root(&db, &mut context, &overlay);
        }
    }

    #[test]
    fn test_overlay_new_account_with_storage() {
        let tmp_dir = TempDir::new("test_overlay_new_account_with_storage").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        let account_address = Address::random();
        let account_path = RawPath::from(AddressPath::for_address(account_address));
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        db.storage_engine
            .set_values(
                &mut context,
                &mut [(account_path, Some(TrieValue::Account(account.clone())))],
            )
            .unwrap();

        let mut overlay_mut = OverlayStateMut::new();
        let new_address = Address::random();
        let new_account_path = AddressPath::for_address(new_address);
        let new_account = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        overlay_mut.insert(
            RawPath::from(&new_account_path),
            Some(OverlayValue::Account(new_account.clone())),
        );

        let storage_key1 = B256::right_padding_from(&[1, 1, 2, 3]);
        let storage_path1 = RawPath::from(StoragePath::for_address_path_and_slot_hash(
            new_account_path.clone(),
            Nibbles::unpack(storage_key1),
        ));
        let storage_value1 = U256::from(123);
        overlay_mut.insert(storage_path1, Some(OverlayValue::Storage(storage_value1)));

        let storage_key2 = B256::right_padding_from(&[1, 1, 2, 0]);
        let storage_path2 = RawPath::from(StoragePath::for_address_path_and_slot_hash(
            new_account_path.clone(),
            Nibbles::unpack(storage_key2),
        ));
        let storage_value2 = U256::from(234);
        overlay_mut.insert(storage_path2, Some(OverlayValue::Storage(storage_value2)));

        let storage_key3 = B256::right_padding_from(&[2, 2, 0, 0]);
        let storage_path3 = RawPath::from(StoragePath::for_address_path_and_slot_hash(
            new_account_path.clone(),
            Nibbles::unpack(storage_key3),
        ));
        let storage_value3 = U256::from(345);
        overlay_mut.insert(storage_path3, Some(OverlayValue::Storage(storage_value3)));

        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
    }

    #[test]
    fn test_overlay_update_account_with_storage() {
        let tmp_dir = TempDir::new("test_overlay_update_account_with_storage").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        let account_address = Address::random();
        let account_path = RawPath::from(AddressPath::for_address(account_address));
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let storage_key1 = U256::from(42);
        let storage_key2 = U256::from(43);
        let storage_path1 =
            RawPath::from(StoragePath::for_address_and_slot(account_address, storage_key1.into()));
        let storage_path2 =
            RawPath::from(StoragePath::for_address_and_slot(account_address, storage_key2.into()));

        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (account_path, Some(TrieValue::Account(account.clone()))),
                    (storage_path1, Some(TrieValue::Storage(U256::from(111)))),
                    (storage_path2, Some(TrieValue::Storage(U256::from(222)))),
                ],
            )
            .unwrap();

        let mut overlay_mut = OverlayStateMut::new();
        let new_account = Account::new(1, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        overlay_mut.insert(account_path, Some(OverlayValue::Account(new_account)));
        overlay_mut.insert(storage_path1, Some(OverlayValue::Storage(U256::from(333))));

        let overlay = overlay_mut.freeze();

        compare_overlay_with_committed_root(&db, &mut context, &overlay);
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
        let storage1_path = RawPath::from(StoragePath::for_address_path_and_slot_hash(
            account_path.clone(),
            Nibbles::from_nibbles(storage1_nibbles),
        ));

        // Second storage path: 0x340123bb...bb (remaining 60 nibbles are 'b')
        let mut storage2_nibbles = vec![0x3, 0x4, 0x0, 0x0, 0x0, 0x0]; // 6 nibbles
        storage2_nibbles.extend(vec![0xb; 58]); // Fill remaining 58 nibbles with 'b' to make 64 total
        let storage2_path = RawPath::from(StoragePath::for_address_path_and_slot_hash(
            account_path.clone(),
            Nibbles::from_nibbles(storage2_nibbles),
        ));

        // Third storage path: 0x3411...11 (remaining 62 nibbles are '1')
        let mut storage3_nibbles = vec![0x3, 0x4, 0x1]; // 3 nibbles
        storage3_nibbles.extend(vec![0x1; 61]); // Fill remaining 61 nibbles with '1' to make 64 total
        let storage3_path = RawPath::from(StoragePath::for_address_path_and_slot_hash(
            account_path.clone(),
            Nibbles::from_nibbles(storage3_nibbles),
        ));

        // Set up initial state with the account and storage that creates the branch structure
        db.storage_engine
            .set_values(
                &mut context,
                &mut [
                    (RawPath::from(&account_path), Some(TrieValue::Account(account.clone()))),
                    (storage1_path, Some(TrieValue::Storage(U256::from(111)))),
                    (storage2_path, Some(TrieValue::Storage(U256::from(222)))),
                    (storage3_path, Some(TrieValue::Storage(U256::from(333)))),
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
        let overlay_storage_path = RawPath::from(StoragePath::for_address_path_and_slot_hash(
            account_path.clone(),
            overlay_storage_nibbles,
        ));

        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(overlay_storage_path, Some(OverlayValue::Storage(U256::from(999))));
        let overlay = overlay_mut.freeze();

        // This triggered a panic due to lexicographic ordering violation
        // The branch node at path ending in 0x340 will be added after its descendant
        // at path ending in 0x34044c6a65488ba0051b7669dae97b8b1fe0cdbb72351b0ca7b4dc42f50dd9b8
        compare_overlay_with_committed_root(&db, &mut context, &overlay);
    }

    #[test]
    fn test_overlay_root_with_branch_node_prefix_ordering_bug() {
        let tmp_dir =
            TempDir::new("test_overlay_root_with_branch_node_prefix_ordering_bug").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let mut context = db.storage_engine.write_context();

        let account_path = AddressPath::new(Nibbles::from_nibbles([
            0x4, 0x5, 0x7, 0x0, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,
            0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,
            0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,
            0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,
        ]));
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        db.storage_engine
            .set_values(
                &mut context,
                &mut [(account_path.into(), Some(TrieValue::Account(account.clone())))],
            )
            .unwrap();

        let account_path2 = AddressPath::new(Nibbles::from_nibbles([
            0x4, 0x5, 0x7, 0x0, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2,
            0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2,
            0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2,
            0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2,
        ]));

        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(
            RawPath::from_nibbles(&[0x4, 0x5, 0x7, 0x0]),
            Some(OverlayValue::Hash(B256::random())),
        );
        overlay_mut.insert(
            account_path2.clone().into(),
            Some(OverlayValue::Account(Account::new(
                2,
                U256::from(200),
                EMPTY_ROOT_HASH,
                KECCAK_EMPTY,
            ))),
        );
        let overlay = overlay_mut.freeze();

        let initial_root = context.root_node_hash;
        // This triggered a panic due to the addition of a leaf node after adding an ancestor branch
        // node.
        let output = db.storage_engine.compute_state_root_with_overlay(&context, overlay).unwrap();
        let (overlay_root, _, _) =
            (output.root, output.updated_branch_nodes, output.storage_branch_updates);
        assert_ne!(overlay_root, initial_root, "Overlay should not match initial root");
    }
}
