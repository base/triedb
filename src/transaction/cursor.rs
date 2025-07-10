use std::ops::Deref;

use alloy_primitives::B256;
use alloy_trie::{nodes::RlpNode, Nibbles};

use crate::{
    location::Location,
    node::{encode_branch, Node, NodeKind},
    page::PageId,
    transaction::{Transaction, RO},
    Database,
};

#[derive(Debug)]
pub struct Cursor<DB: Deref<Target = Database>> {
    transaction: Transaction<DB, RO>,
    account_key: Option<B256>,
    loc_stack: Vec<Location>,
    page_id_stack: Vec<PageId>,
    node_stack: Vec<Node>,
    key_stack: Vec<Nibbles>,
    hash_stack: Vec<B256>,
    initialized: bool,
}

#[derive(Debug)]
pub enum CursorError {
    InvalidKey,
}

impl<DB: Deref<Target = Database>> Cursor<DB> {
    pub fn new_account_cursor(transaction: Transaction<DB, RO>) -> Self {
        Self::new_with_account_key(transaction, None)
    }

    pub fn new_storage_cursor(transaction: Transaction<DB, RO>, account_key: B256) -> Self {
        Self::new_with_account_key(transaction, Some(account_key))
    }

    fn new_with_account_key(transaction: Transaction<DB, RO>, account_key: Option<B256>) -> Self {
        Self {
            transaction,
            account_key,
            loc_stack: Vec::new(),
            page_id_stack: Vec::new(),
            node_stack: Vec::new(),
            key_stack: Vec::new(),
            hash_stack: Vec::new(),
            initialized: false,
        }
    }

    /// Return the current key and node.
    pub fn current(&self) -> Option<(&Nibbles, &Node, B256)> {
        self.current_key_node_and_hash()
    }

    /// Move the cursor to the next key.
    pub fn next(&mut self) -> Result<Option<(&Nibbles, &Node, B256)>, CursorError> {
        if !self.initialized {
            self.initialized = true;
            return self.start_from_root();
        }

        match self.current_node() {
            Some(node) => {
                match node.kind() {
                    NodeKind::Branch { .. } => self.traverse_branch_children(),
                    NodeKind::AccountLeaf { .. } | NodeKind::StorageLeaf { .. } => self.backtrack_from_leaf(),
                }
            }
            None => Ok(None),
        }
    }

    /// Move the cursor to the key and return a value matching or greater than the key.
    pub fn seek(&mut self, key: &Nibbles) -> Result<Option<(&Nibbles, &Node, B256)>, CursorError> {
        let result = self.seek_internal(key);
        if let Some((new_key, _, _)) = result.as_ref().unwrap() {
            assert!(*new_key >= key, "TrieDB Cursor seek returned a key less than the target key");
        }

        result
    }

    fn seek_internal(
        &mut self,
        key: &Nibbles,
    ) -> Result<Option<(&Nibbles, &Node, B256)>, CursorError> {
        // If not initialized, start from root
        if !self.initialized || !self.has_current() {
            self.initialized = true;
            match self.start_from_root()? {
                Some((new_key, _, _)) => {
                    // If the new key is greater than or equal to the target key, return it
                    if new_key >= key {
                        return Ok(self.current());
                    }
                }
                None => return Ok(None),
            }
        }

        let current_key = self.current_key().unwrap();

        // If we're already at the target key, return current position
        if current_key == key {
            return Ok(self.current());
        }

        // Find the longest common prefix between current position and target
        let common_prefix_len = Nibbles::common_prefix_length(current_key, key);

        // Optimize: backtrack only to the point where paths diverge
        self.backtrack_to_common_ancestor(common_prefix_len)?;

        assert!(self.has_current(), "TrieDB Cursor seek backtracked to empty node");

        // Continue seeking from the common ancestor
        self.seek_recursive(key)
    }

    /// Backtrack the cursor to the common ancestor at the given prefix length
    fn backtrack_to_common_ancestor(
        &mut self,
        target_prefix_len: usize,
    ) -> Result<(), CursorError> {
        // Keep popping until we reach a key that is a prefix of the target length or we've popped
        // all the way to the root
        while let Some(current_key) = self.current_key() {
            if current_key.len() <= target_prefix_len || self.node_stack.len() <= 1 {
                break;
            }

            // Pop one level
            let current_loc = self.loc_stack.pop().unwrap();
            if current_loc.page_id().is_some() {
                self.page_id_stack.pop();
            }
            self.node_stack.pop();
            self.key_stack.pop();
            self.hash_stack.pop();
        }

        Ok(())
    }

    /// Recursively navigate through the tree to find the target key or next higher key
    fn seek_recursive(
        &mut self,
        target_key: &Nibbles,
        // path_offset: usize,
    ) -> Result<Option<(&Nibbles, &Node, B256)>, CursorError> {
        let current_key = self.current_key().unwrap();
        // If the current key is not a prefix of the target key, we need to find the next higher key
        if !target_key.has_prefix(current_key) {
            return self.find_next_higher_key_from_current_level(target_key);
        }

        // If we've consumed the entire target key, this is our result
        if current_key.len() >= target_key.len() {
            return Ok(self.current());
        }

        let current_node = self.current_node().unwrap();

        // Handle different node types
        match current_node.kind() {
            NodeKind::Branch { .. } => {
                // This is a branch node, navigate to the appropriate child
                let next_nibble = target_key[current_key.len()];

                // Try to find a child at or after the target nibble
                for child_index in next_nibble..16 {
                    if let Some(child_pointer) = current_node.child(child_index).unwrap() {
                        // Load the child and continue recursion
                        let child_hash = child_pointer.rlp().as_hash().unwrap_or_default();
                        self.load_child_node_into_stack(
                            child_pointer.location(),
                            current_key.clone(),
                            Some(child_index),
                            child_hash,
                        )?;
                        if child_index == next_nibble {
                            // This is the exact path we want, continue recursion
                            return self.seek_recursive(target_key);
                        } else {
                            // This child is higher than our target, return it
                            return Ok(self.current());
                        }
                    }
                }

                // No suitable child found at this level, backtrack to find next higher key
                self.backtrack_to_find_next_higher_key(target_key)
            }
            NodeKind::AccountLeaf { .. } | NodeKind::StorageLeaf { .. } => self.backtrack_from_leaf(),
        }
    }

    /// Find the next higher key when current node's prefix doesn't match target
    fn find_next_higher_key_from_current_level(
        &mut self,
        target_key: &Nibbles,
    ) -> Result<Option<(&Nibbles, &Node, B256)>, CursorError> {
        // Check if current key is already >= target
        if self.key_stack.last().unwrap() >= target_key {
            return Ok(self.current());
        }

        // Otherwise, backtrack to find next higher key
        self.backtrack_to_find_next_higher_key(target_key)
    }

    /// Backtrack through the stack to find the next higher key
    fn backtrack_to_find_next_higher_key(
        &mut self,
        target_key: &Nibbles,
    ) -> Result<Option<(&Nibbles, &Node, B256)>, CursorError> {
        // Pop current node since it doesn't satisfy our condition
        if !self.key_stack.is_empty() {
            let current_loc = self.loc_stack.pop().unwrap();
            if current_loc.page_id().is_some() {
                self.page_id_stack.pop();
            }
            self.node_stack.pop();
            self.key_stack.pop();
            self.hash_stack.pop();
        }

        // If we've backtracked to empty, no higher key exists
        if self.node_stack.is_empty() {
            return Ok(None);
        }

        let parent_node = self.current_node().unwrap();

        // If this is not a branch, continue backtracking
        if !parent_node.is_branch() {
            return self.backtrack_to_find_next_higher_key(target_key);
        }

        let parent_key = self.current_key().unwrap();

        // Find the next sibling that might contain a higher key
        let current_child_index = if parent_key.len() < target_key.len() {
            target_key[parent_key.len()]
        } else {
            15 // If we've consumed the target, look for any remaining children
        };

        // Look for the next available child at or after current_child_index
        for child_index in (current_child_index + 1)..16 {
            if let Some(child_pointer) = parent_node.child(child_index).unwrap() {
                let child_hash = child_pointer.rlp().as_hash().unwrap_or_default();
                self.load_child_node_into_stack(
                    child_pointer.location(),
                    parent_key.clone(),
                    Some(child_index),
                    child_hash,
                )?;
                return Ok(self.current());
            }
        }

        // No suitable sibling found, continue backtracking
        self.backtrack_to_find_next_higher_key(target_key)
    }

    /// Load a child node from either the same page or a different page
    fn load_child_node_into_stack(
        &mut self,
        child_location: Location,
        parent_key: Nibbles,
        child_index: Option<u8>,
        child_hash: B256,
    ) -> Result<(), CursorError> {
        self.loc_stack.push(child_location);

        if child_location.page_id().is_some() {
            self.page_id_stack.push(child_location.page_id().unwrap());
        }

        let child_page_id = *self.page_id_stack.last().unwrap();

        let child_slotted_page = self
            .transaction
            .get_slotted_page(child_page_id)
            .map_err(|_| CursorError::InvalidKey)?;

        let child_node: Node = if child_location.cell_index().is_some() {
            child_slotted_page
                .get_value(child_location.cell_index().unwrap())
                .map_err(|_| CursorError::InvalidKey)?
        } else {
            child_slotted_page.get_value(0).unwrap()
        };

        let child_key = Self::build_child_key(parent_key, child_index, &child_node);
        self.key_stack.push(child_key);
        self.node_stack.push(child_node);
        self.hash_stack.push(child_hash);

        Ok(())
    }

    /// Build the full key for a child node
    fn build_child_key(parent_key: Nibbles, child_index: Option<u8>, child_node: &Node) -> Nibbles {
        let mut child_key = parent_key;
        if let Some(child_index) = child_index {
            child_key.push(child_index);
        }
        child_key.extend_from_slice(child_node.prefix());
        child_key
    }

    fn has_current(&self) -> bool {
        !self.key_stack.is_empty()
    }

    fn current_key(&self) -> Option<&Nibbles> {
        self.key_stack.last()
    }

    fn current_node(&self) -> Option<&Node> {
        self.node_stack.last()
    }

    /// Get the current key and node from the stack
    fn current_key_node_and_hash(&self) -> Option<(&Nibbles, &Node, B256)> {
        match (self.key_stack.last(), self.node_stack.last(), self.hash_stack.last()) {
            (Some(key), Some(node), Some(hash)) => {
                match node.kind() {
                    NodeKind::Branch { children, .. } => {
                        if !node.prefix().is_empty() {
                            // we will need to hash this node directly, as the parent pointer has
                            // the hash of the implied extension node
                            let mut buf = [0u8; 3 + 33 * 16 + 1]; // max RLP length for a branch: 3 bytes for the list length, 33 bytes
                                                                  // for each
                            let mut branch_rlp = buf.as_mut();
                            let branch_rlp_length = encode_branch(children, &mut branch_rlp);
                            let node_rlp = RlpNode::from_rlp(&buf[..branch_rlp_length]);
                            let node_hash = node_rlp.as_hash().unwrap_or_default();
                            Some((key, node, node_hash))
                        } else {
                            Some((key, node, *hash))
                        }
                    }
                    _ => Some((key, node, *hash)),
                }
            }
            _ => None,
        }
    }

    /// Initialize cursor from root node
    fn start_from_root(&mut self) -> Result<Option<(&Nibbles, &Node, B256)>, CursorError> {
        if self.transaction.context.root_node_page_id.is_none() {
            return Ok(None);
        }

        let root_node_page_id = self.transaction.context.root_node_page_id.unwrap();
        let root_slotted_page = self
            .transaction
            .get_slotted_page(root_node_page_id)
            .map_err(|_| CursorError::InvalidKey)?;
        let root_node: Node = root_slotted_page.get_value(0).unwrap();
        let root_key = root_node.prefix().clone();
        let root_hash = self.transaction.context.root_node_hash;

        self.loc_stack.push(Location::for_page(root_node_page_id));
        self.page_id_stack.push(root_node_page_id);
        self.node_stack.push(root_node);
        self.key_stack.push(root_key);
        self.hash_stack.push(root_hash);

        if let Some(account_key) = self.account_key {
            let result = self.seek(&Nibbles::unpack(account_key))?;
            match result {
                Some((key, _, _)) => {
                    if key == &Nibbles::unpack(account_key) {
                        self.initialize_storage_stacks()?;
                        return Ok(self.current());
                    } else {
                        return Ok(None);
                    }
                }
                None => {
                    return Ok(None);
                }
            }
        }

        let key_ref = self.key_stack.last().unwrap();
        let node_ref = self.node_stack.last().unwrap();
        let hash_ref = *self.hash_stack.last().unwrap();
        Ok(Some((key_ref, node_ref, hash_ref)))
    }

    fn initialize_storage_stacks(&mut self) -> Result<(), CursorError> {
        let current_key = self.current_key().unwrap();
        let current_node = self.current_node().unwrap();
        let storage_root = current_node.direct_child().unwrap();
        if storage_root.is_none() {
            self.loc_stack.clear();
            self.page_id_stack.clear();
            self.node_stack.clear();
            self.key_stack.clear();
            self.hash_stack.clear();
            return Ok(());
        }

        let storage_root_pointer = storage_root.unwrap();
        let storage_root_hash = storage_root_pointer.rlp().as_hash().unwrap_or_default();
        self.load_child_node_into_stack(
            storage_root_pointer.location(),
            current_key.clone(),
            None,
            storage_root_hash,
        )?;

        let storage_root_loc = self.loc_stack.pop().unwrap();
        self.loc_stack.clear();
        self.loc_stack.push(storage_root_loc);

        let storage_root_page_id = self.page_id_stack.pop().unwrap();
        self.page_id_stack.clear();
        self.page_id_stack.push(storage_root_page_id);

        let storage_root_node = self.node_stack.pop().unwrap();
        let storage_root_key = storage_root_node.prefix().clone();
        let storage_root_hash = self.hash_stack.pop().unwrap();

        self.node_stack.clear();
        self.node_stack.push(storage_root_node);

        self.key_stack.clear();
        self.key_stack.push(storage_root_key);

        self.hash_stack.clear();
        self.hash_stack.push(storage_root_hash);

        Ok(())
    }

    /// Traverse children of a branch node
    fn traverse_branch_children(&mut self) -> Result<Option<(&Nibbles, &Node, B256)>, CursorError> {
        let parent_key = self.current_key().unwrap();
        let parent_node = self.current_node().unwrap();

        for child_index in 0..16 {
            let child = parent_node.child(child_index).unwrap();
            if child.is_none() {
                continue;
            }

            let child_pointer = child.as_ref().unwrap();
            let child_hash = child_pointer.rlp().as_hash().unwrap_or_else(|| {
                // If not a hash reference, compute hash from the node itself
                let child_page_id = if child_pointer.location().page_id().is_some() {
                    child_pointer.location().page_id().unwrap()
                } else {
                    *self.page_id_stack.last().unwrap()
                };
                let child_slotted_page = self.transaction.get_slotted_page(child_page_id).unwrap();
                let child_node: Node = if child_pointer.location().cell_index().is_some() {
                    child_slotted_page
                        .get_value(child_pointer.location().cell_index().unwrap())
                        .unwrap()
                } else {
                    child_slotted_page.get_value(0).unwrap()
                };
                child_node.to_rlp_node().as_hash().unwrap()
            });
            self.load_child_node_into_stack(
                child_pointer.location(),
                parent_key.clone(),
                Some(child_index),
                child_hash,
            )?;
            return Ok(self.current());
        }

        // No children found, backtrack
        self.backtrack_to_next_sibling()
    }

    /// Backtrack to find the next sibling at any level
    fn backtrack_to_next_sibling(
        &mut self,
    ) -> Result<Option<(&Nibbles, &Node, B256)>, CursorError> {
        while !self.node_stack.is_empty() {
            // Pop current node
            let current_loc = self.loc_stack.pop().unwrap();
            if current_loc.page_id().is_some() {
                self.page_id_stack.pop();
            }
            self.node_stack.pop();
            let current_key = self.key_stack.pop().unwrap();
            self.hash_stack.pop();

            // If we've reached the root, we're done
            if self.node_stack.is_empty() {
                return Ok(None);
            }

            let parent_key = self.key_stack.last().unwrap().clone();

            // Get current child index and try to find next sibling
            let current_child_index = current_key.get(parent_key.len()).unwrap();

            if self.find_next_sibling_from_index(current_child_index + 1)? {
                return Ok(self.current());
            }

            // No sibling found, continue backtracking
        }

        Ok(None)
    }

    /// Find the next sibling starting from the given index
    fn find_next_sibling_from_index(&mut self, start_index: u8) -> Result<bool, CursorError> {
        let parent_node = self.current_node().unwrap();
        let children = match parent_node.kind() {
            NodeKind::Branch { children, .. } => children,
            _ => return Ok(false),
        };
        let parent_key = self.current_key().unwrap();

        for child_index in start_index..16 {
            if children[child_index as usize].is_none() {
                continue;
            }

            let child_pointer = children[child_index as usize].as_ref().unwrap();
            let child_hash = child_pointer.rlp().as_hash().unwrap_or_else(|| {
                // If not a hash reference, compute hash from the node itself
                let child_page_id = if child_pointer.location().page_id().is_some() {
                    child_pointer.location().page_id().unwrap()
                } else {
                    *self.page_id_stack.last().unwrap()
                };
                let child_slotted_page = self.transaction.get_slotted_page(child_page_id).unwrap();
                let child_node: Node = if child_pointer.location().cell_index().is_some() {
                    child_slotted_page
                        .get_value(child_pointer.location().cell_index().unwrap())
                        .unwrap()
                } else {
                    child_slotted_page.get_value(0).unwrap()
                };
                child_node.to_rlp_node().as_hash().unwrap()
            });
            self.load_child_node_into_stack(
                child_pointer.location(),
                parent_key.clone(),
                Some(child_index),
                child_hash,
            )?;
            return Ok(true);
        }

        Ok(false)
    }

    /// Backtrack from a leaf node
    fn backtrack_from_leaf(&mut self) -> Result<Option<(&Nibbles, &Node, B256)>, CursorError> {
        // Pop current leaf node from stacks
        let current_loc = self.loc_stack.pop().unwrap();
        if current_loc.page_id().is_some() {
            self.page_id_stack.pop();
        }
        self.node_stack.pop();
        let mut child_key = self.key_stack.pop().unwrap();
        self.hash_stack.pop();

        // Now continue backtracking until we find a parent with a next sibling
        while !self.node_stack.is_empty() {
            let parent_key = self.key_stack.last().unwrap();

            // Get the current child index from the child_key
            let current_child_index = child_key.get(parent_key.len()).unwrap();

            // Try to find the next sibling
            if self.find_next_sibling_from_index(current_child_index + 1)? {
                return Ok(self.current());
            }

            // No sibling found at this level, backtrack further
            let current_loc = self.loc_stack.pop().unwrap();
            if current_loc.page_id().is_some() {
                self.page_id_stack.pop();
            }
            self.node_stack.pop();
            child_key = self.key_stack.pop().unwrap();
            self.hash_stack.pop();
        }

        // Reached root with no more siblings
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use alloy_primitives::{Address, B256, U256};
    use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
    use tempdir::TempDir;

    use crate::{
        account::Account,
        database::begin_rw,
        path::{AddressPath, StoragePath},
        Database,
    };

    use super::*;

    #[test]
    fn test_single_account_cursor() {
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        let address_path = AddressPath::new(Nibbles::from_vec(vec![1; 64]));
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let mut early_cursor = Cursor::new_account_cursor(db.begin_ro().unwrap());

        let mut tx = db.begin_rw().unwrap();
        tx.set_account(address_path.clone(), Some(account.clone())).unwrap();
        tx.commit().unwrap();

        // early cursor should not see the account
        assert!(early_cursor.next().unwrap().is_none());

        let mut cursor = Cursor::new_account_cursor(db.begin_ro().unwrap());
        let root_hash = cursor.transaction.context.root_node_hash;

        // first item found is the single account leaf node
        let result = cursor.next();
        assert!(result.is_ok());
        let (key, node, hash) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![1; 64]));
        assert!(matches!(node.kind(), NodeKind::AccountLeaf { .. }), "node: {:?}", node);

        // Verify the hash is correct - for root node it should match the context's root hash
        assert_eq!(hash, root_hash, "Hash should match the root node hash from context");

        // Also verify the hash matches what we'd compute from the node itself
        let computed_hash = node.to_rlp_node().as_hash().unwrap();
        assert_eq!(hash, computed_hash, "Hash should match the computed hash from node RLP");

        // next item found is none
        let result = cursor.next();
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());

        // seek to the same key as the first item
        let result = cursor.seek(&Nibbles::from_vec(vec![1; 64]));
        assert!(result.is_ok());
        let (key, node, hash) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![1; 64]));
        assert!(matches!(node.kind(), NodeKind::AccountLeaf { .. }), "node: {:?}", node);

        // Verify hash again after seek
        assert_eq!(
            hash, cursor.transaction.context.root_node_hash,
            "Hash should still match the root node hash after seek"
        );

        // seek to a key that is less than the first item
        let result = cursor.seek(&Nibbles::from_vec(vec![0; 64]));
        assert!(result.is_ok());
        let (key, node, hash) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![1; 64]));
        assert!(matches!(node.kind(), NodeKind::AccountLeaf { .. }), "node: {:?}", node);

        // Verify hash for this case too
        assert_eq!(
            hash, cursor.transaction.context.root_node_hash,
            "Hash should match the root node hash"
        );

        // seek to a key that is greater than the first item
        let result = cursor.seek(&Nibbles::from_vec(vec![15; 64]));
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_account_cursor() {
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();
        let mut tx = db.begin_rw().unwrap();

        // top branch has 2 children, one is a leaf and the other is a branch with 2 children

        let address_path1 = AddressPath::new(Nibbles::from_vec(vec![1; 64]));
        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let address_path2 = AddressPath::new(Nibbles::from_vec(vec![2; 64]));
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let addr2_storage1 =
            StoragePath::for_address_path_and_slot(address_path2.clone(), B256::from([0x01; 32]));

        let address_path3 = AddressPath::new(Nibbles::from_vec(
            vec![2, 2].into_iter().chain(vec![3; 62]).collect::<Vec<_>>(),
        ));
        let account3 = Account::new(3, U256::from(300), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        tx.set_account(address_path1.clone(), Some(account1.clone())).unwrap();
        tx.set_account(address_path2.clone(), Some(account2.clone())).unwrap();
        tx.set_storage_slot(addr2_storage1.clone(), Some(U256::from(123))).unwrap();
        tx.set_account(address_path3.clone(), Some(account3.clone())).unwrap();
        tx.commit().unwrap();

        let mut cursor = Cursor::new_account_cursor(db.begin_ro().unwrap());
        let root_hash = cursor.transaction.context.root_node_hash;

        // first item found is the root node (branch)
        let result = cursor.next();
        let (key, branch_node, hash) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::default());
        assert_eq!(branch_node.prefix(), &Nibbles::default());
        assert!(branch_node.child(1).unwrap().is_some());
        assert!(branch_node.child(2).unwrap().is_some());

        // Verify the root hash matches the context
        assert_eq!(hash, root_hash, "Root node hash should match context");

        // Verify the hash matches the computed hash
        let computed_hash = branch_node.to_rlp_node().as_hash().unwrap();
        assert_eq!(hash, computed_hash, "Root hash should match computed hash");

        // Store the parent pointer for later verification before borrowing cursor again
        let parent_child_pointer = branch_node.child(1).unwrap().unwrap().clone();

        // second item found is the first account leaf node
        let result = cursor.next();
        let (key, leaf_node, hash) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![1; 64]));
        assert_eq!(leaf_node.prefix(), &Nibbles::from_vec(vec![1; 63]));
        assert!(matches!(leaf_node.kind(), NodeKind::AccountLeaf { .. }));

        // Verify this child's hash matches what's stored in the parent's pointer
        let expected_child_hash = parent_child_pointer.rlp().as_hash().unwrap();
        assert_eq!(hash, expected_child_hash, "Child hash should match parent's pointer hash");

        // Also verify it matches the computed hash
        let computed_child_hash = leaf_node.to_rlp_node().as_hash().unwrap();
        assert_eq!(hash, computed_child_hash, "Child hash should match computed hash");

        // current also returns the first account leaf node
        let result = cursor.current();
        assert!(result.is_some());
        let (key, leaf_node, hash) = result.unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![1; 64]));
        assert_eq!(leaf_node.prefix(), &Nibbles::from_vec(vec![1; 63]));
                assert!(matches!(leaf_node.kind(), NodeKind::AccountLeaf { .. }));

        // Verify hash consistency in current() as well
        let computed_hash = leaf_node.to_rlp_node().as_hash().unwrap();
        assert_eq!(hash, computed_hash, "Current() should return consistent hash");

        // next item found is the nested branch node
        let result = cursor.next();
        let (key, branch_node, hash) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![2, 2]));
        assert_eq!(branch_node.prefix(), &Nibbles::from_vec(vec![2]));
        assert!(branch_node.child(2).unwrap().is_some());
        assert!(branch_node.child(3).unwrap().is_some());

        // Verify this nested branch hash
        let computed_hash = branch_node.to_rlp_node().as_hash().unwrap();
        assert_ne!(hash, computed_hash, "Nested branch hash should NOT match computed hash, as the computed_hash is for the extension node");

        // next item found is the second account leaf node
        let result = cursor.next();
        let (key, leaf_node, hash) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![2; 64]));
        assert_eq!(leaf_node.prefix(), &Nibbles::from_vec(vec![2; 61]));
        assert!(matches!(leaf_node.kind(), NodeKind::AccountLeaf { .. }));

        // Verify this leaf's hash
        let computed_hash = leaf_node.to_rlp_node().as_hash().unwrap();
        assert_eq!(hash, computed_hash, "Second leaf hash should match computed hash");

        // next item found is the third account leaf node (skipping the second account's storage)
        let result = cursor.next();
        let (key, leaf_node, hash) = result.unwrap().unwrap();
        assert_eq!(
            key,
            &Nibbles::from_vec(vec![2, 2].into_iter().chain(vec![3; 62]).collect::<Vec<_>>())
        );
        assert_eq!(leaf_node.prefix(), &Nibbles::from_vec(vec![3; 61]));
        assert!(matches!(leaf_node.kind(), NodeKind::AccountLeaf { .. }));

        // Verify this leaf's hash
        let computed_hash = leaf_node.to_rlp_node().as_hash().unwrap();
        assert_eq!(hash, computed_hash, "Third leaf hash should match computed hash");

        // no more account trie nodes found
        let result = cursor.next();
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_single_storage_cursor() {
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Arc::new(Database::create_new(file_path).unwrap());

        let address_path = AddressPath::for_address(Address::from([0x42; 20]));
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let storage_key = Nibbles::from_vec(vec![1; 64]);
        let storage_value = U256::from(0x1111);

        let mut tx = begin_rw(db.clone()).unwrap();
        tx.set_account(address_path.clone(), Some(account.clone())).unwrap();
        tx.set_storage_slot(
            StoragePath::for_address_path_and_slot_hash(address_path.clone(), storage_key.clone()),
            Some(storage_value.clone()),
        )
        .unwrap();
        let mut early_cursor = tx.new_storage_cursor(address_path.clone().into());
        tx.commit().unwrap();

        // The cursor should be empty because it was created before the commit
        let result = early_cursor.next();
        assert!(result.unwrap().is_none());

        let mut cursor = db.begin_ro().unwrap().new_storage_cursor(address_path.into());

        // first item found is the storage leaf node
        let result = cursor.next();
        assert!(result.is_ok());
        let (key, node, hash) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![1; 64]));
        assert!(matches!(node.kind(), NodeKind::StorageLeaf { .. }), "node: {:?}", node);

        // Verify the hash matches the computed hash for storage leaf
        let computed_hash = node.to_rlp_node().as_hash().unwrap();
        assert_eq!(hash, computed_hash, "Storage leaf hash should match computed hash");

        // seek to the same key as the first item
        let result = cursor.seek(&Nibbles::from_vec(vec![1; 64]));
        assert!(result.is_ok());
        let (key, node, hash) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![1; 64]));
        assert!(matches!(node.kind(), NodeKind::StorageLeaf { .. }), "node: {:?}", node);

        // Verify hash consistency after seek
        let computed_hash = node.to_rlp_node().as_hash().unwrap();
        assert_eq!(hash, computed_hash, "Storage leaf hash should be consistent after seek");

        // seek to a key that is less than the first item
        let result = cursor.seek(&Nibbles::from_vec(vec![0; 64]));
        assert!(result.is_ok());
        let (key, node, hash) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![1; 64]));
        assert!(matches!(node.kind(), NodeKind::StorageLeaf { .. }), "node: {:?}", node);

        // Verify hash for this case too
        let computed_hash = node.to_rlp_node().as_hash().unwrap();
        assert_eq!(hash, computed_hash, "Storage leaf hash should match computed hash");

        // seek to a key that is greater than the first item
        let result = cursor.seek(&Nibbles::from_vec(vec![15; 64]));
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_storage_cursor() {
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        // Create an account
        let address = Address::from([0x42; 20]);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account_path = AddressPath::for_address(address);

        // Create storage slots for the account
        let storage_key1 = B256::from([0x01; 32]);
        let storage_value1 = U256::from(0x1111);
        let storage_path1 = StoragePath::for_address_and_slot(address, storage_key1);

        let storage_key2 = B256::from([0x02; 32]);
        let storage_value2 = U256::from(0x2222);
        let storage_path2 = StoragePath::for_address_and_slot(address, storage_key2);

        // Set account and storage values
        let mut tx = db.begin_rw().unwrap();
        tx.set_account(account_path.clone(), Some(account.clone())).unwrap();
        tx.set_storage_slot(storage_path1.clone(), Some(storage_value1.clone())).unwrap();
        tx.set_storage_slot(storage_path2.clone(), Some(storage_value2.clone())).unwrap();
        tx.commit().unwrap();

        let mut cursor = Cursor::new_storage_cursor(db.begin_ro().unwrap(), account_path.into());

        // Iterate through all nodes and count what we find
        let mut found_account = false;
        let mut found_storage_nodes = 0;
        let mut found_nodes = 0;

        while let Ok(Some((key, node, _))) = cursor.next() {
            found_nodes += 1;
            match node.kind() {
                NodeKind::AccountLeaf { .. } => {
                    found_account = true;
                }
                NodeKind::StorageLeaf { .. } => {
                    assert_eq!(key.len(), 64);
                    found_storage_nodes += 1;
                }
                _ => {}
            }
        }

        // We should have found the account and storage entries
        assert!(!found_account, "Should not have found the account node");
        assert!(found_storage_nodes > 0, "Should have found storage nodes");
        assert_eq!(found_nodes, 3, "Should have found 3 nodes");
    }

    #[test]
    fn test_storage_cursor_no_account_storage() {
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        // Create an account
        let address = Address::from([0x42; 20]);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account_path = AddressPath::for_address(address);

        // Set account and storage values
        let mut tx = db.begin_rw().unwrap();
        tx.set_account(account_path.clone(), Some(account.clone())).unwrap();
        tx.commit().unwrap();

        let mut cursor = Cursor::new_storage_cursor(db.begin_ro().unwrap(), account_path.into());

        let result = cursor.next();
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());

        let result = cursor.seek(&Nibbles::from_vec(vec![1; 64]));
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());

        let result = cursor.next();
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_account_cursor_seek() {
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        // Create accounts with different patterns to test nearby seeking
        let accounts = vec![
            (vec![1, 0], Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY)),
            (vec![1, 5], Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY)),
            (vec![2, 0], Account::new(3, U256::from(300), EMPTY_ROOT_HASH, KECCAK_EMPTY)),
            (vec![2, 5], Account::new(4, U256::from(400), EMPTY_ROOT_HASH, KECCAK_EMPTY)),
            (vec![3, 0], Account::new(5, U256::from(500), EMPTY_ROOT_HASH, KECCAK_EMPTY)),
        ];

        for (path_vec, account) in &accounts {
            // Pad to 64 nibbles for AddressPath
            let mut full_path = path_vec.clone();
            full_path.extend(vec![0; 62]);
            let path = AddressPath::new(Nibbles::from_vec(full_path));
            let mut tx = db.begin_rw().unwrap();
            tx.set_account(path.clone(), Some(account.clone())).unwrap();
            tx.commit().unwrap();
        }

        let mut cursor = Cursor::new_account_cursor(db.begin_ro().unwrap());

        // First, position the cursor at [1, 0, 0, 0, ...]
        let mut target1 = vec![1, 0];
        target1.extend(vec![0; 62]);
        let result = cursor.seek(&Nibbles::from_vec(target1.clone()));
        let (key, _, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(target1));

        // Now seek to a nearby key [1, 3] - should efficiently find [1, 5, ...]
        // This should reuse the common prefix [1] and not go back to root
        let target2 = vec![1, 3];
        let mut expected2 = vec![1, 5];
        expected2.extend(vec![0; 62]);
        let result = cursor.seek(&Nibbles::from_vec(target2));
        let (key, _, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(expected2));

        // Seek to the exact current location. This should return the current position.
        let same_target = key.clone();
        let result = cursor.seek(&same_target);
        let (key, _, _) = result.unwrap().unwrap();
        assert_eq!(key, &same_target);

        // Now move to the next key, which should be the branch at [2]
        let result = cursor.next();
        let (key, branch_node, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![2]));
        assert_eq!(branch_node.prefix(), &Nibbles::default()); // Branch prefix should be empty
        assert!(branch_node.child(0).unwrap().is_some());
        assert!(branch_node.child(5).unwrap().is_some());

        // Seek to the exact current location. This should return the current position.
        let same_target = key.clone();
        let result = cursor.seek(&same_target);
        let (key, _, _) = result.unwrap().unwrap();
        assert_eq!(key, &same_target);

        // Seek to another nearby key [2, 3, ...] - should find [2, 5, ...]
        let mut target3 = vec![2, 3];
        target3.extend(vec![0; 62]);
        let mut expected3 = vec![2, 5];
        expected3.extend(vec![0; 62]);
        let result = cursor.seek(&Nibbles::from_vec(target3));
        let (key, _, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(expected3.clone()));

        // Seek to the exact current location. This should return the current position.
        let same_target = key.clone();
        let result = cursor.seek(&same_target);
        let (key, _, _) = result.unwrap().unwrap();
        assert_eq!(key, &same_target);

        // Seek backwards to a key we've already passed
        let mut target4 = vec![2, 0];
        target4.extend(vec![0; 62]);
        let mut expected4 = vec![2, 0];
        expected4.extend(vec![0; 62]);
        let result = cursor.seek(&Nibbles::from_vec(target4));
        let (key, _, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(expected4.clone()));

        // Seek to exact current position - should return immediately
        let result = cursor.seek(&Nibbles::from_vec(expected4.clone()));
        let (key, _, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(expected4));

        // Next should be [2, 5, ...]
        let mut expected3 = vec![2, 5];
        expected3.extend(vec![0; 62]);
        let result = cursor.next();
        let (key, _, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(expected3));

        // Next should be [3, 0, ...]
        let mut expected = vec![3];
        expected.extend(vec![0; 63]);
        let result = cursor.next();
        let (key, _, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(expected));

        // Next should be empty
        let result = cursor.next();
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_storage_cursor_seek() {
        use alloy_primitives::{Address, B256, U256};

        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        // Create an account with storage
        let address = Address::from([0x42; 20]);
        let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let account_path = AddressPath::for_address(address);

        // Create storage slots for the account
        let storage_key1 = B256::from([0x01; 32]);
        let storage_value1 = U256::from(0x1111);
        let storage_path1 = StoragePath::for_address_and_slot(address, storage_key1);

        let storage_key2 = B256::from([0x05; 32]);
        let storage_value2 = U256::from(0x2222);
        let storage_path2 = StoragePath::for_address_and_slot(address, storage_key2);

        // Set account and storage values
        let mut tx = db.begin_rw().unwrap();
        tx.set_account(account_path.clone(), Some(account.clone())).unwrap();
        tx.set_storage_slot(storage_path1.clone(), Some(storage_value1.clone())).unwrap();
        tx.set_storage_slot(storage_path2.clone(), Some(storage_value2.clone())).unwrap();
        tx.commit().unwrap();

        let mut cursor = Cursor::new_storage_cursor(db.begin_ro().unwrap(), account_path.into());

        // Seek to an empty path (should find the root branch)
        let result = cursor.seek(&Nibbles::default());
        assert!(result.is_ok());
        let result = result.unwrap();
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, &Nibbles::default());
        assert!(matches!(result.unwrap().1.kind(), NodeKind::Branch { .. }));

        // Seek to the first storage slot
        let result = cursor.seek(storage_path1.get_slot());
        assert!(result.is_ok());
        let result = result.unwrap();
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, storage_path1.get_slot());

        // Seek to the storage slot defined by all zero bytes (should find next higher)
        let missing_storage_key = B256::from([0x00; 32]);
        let result = cursor.seek(&Nibbles::unpack(missing_storage_key));
        assert!(result.is_ok());
        let result = result.unwrap();
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, storage_path1.get_slot());

        // Seek to a storage slot that doesn't exist (should find next higher)
        let missing_storage_key = B256::from([0x03; 32]);
        let result = cursor.seek(&Nibbles::unpack(missing_storage_key));
        assert!(result.is_ok());
        let result = result.unwrap();
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, storage_path1.get_slot());

        // Seek to the very end of the storage trie (should find nothing)
        let result = cursor.seek(&Nibbles::from_vec(vec![0x0F; 32]));
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_cursor_hash_verification() {
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create_new(file_path).unwrap();

        // Create a simple tree structure for hash verification
        let address_path1 = AddressPath::new(Nibbles::from_vec(vec![1; 64]));
        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let address_path2 = AddressPath::new(Nibbles::from_vec(vec![2; 64]));
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let mut tx = db.begin_rw().unwrap();
        tx.set_account(address_path1.clone(), Some(account1.clone())).unwrap();
        tx.set_account(address_path2.clone(), Some(account2.clone())).unwrap();
        tx.commit().unwrap();

        let mut cursor = Cursor::new_account_cursor(db.begin_ro().unwrap());

        // Test 1: Root node hash verification
        let result = cursor.next();
        assert!(result.is_ok());
        let (_key, root_node, root_hash) = result.unwrap().unwrap();

        // Root should match context hash
        assert_eq!(root_hash, root_hash, "Root hash must match context");

        // Root should match computed hash
        let computed_root_hash = root_node.to_rlp_node().as_hash().unwrap();
        assert_eq!(root_hash, computed_root_hash, "Root hash must match computed hash");

        // Store child pointers for verification
        let child1_pointer = root_node.child(1).unwrap().unwrap().clone();
        let child2_pointer = root_node.child(2).unwrap().unwrap().clone();

        // Test 2: First child hash verification
        let result = cursor.next();
        assert!(result.is_ok());
        let (key, child1_node, child1_hash) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![1; 64]));

        // Child hash should match parent's pointer
        let expected_child1_hash = child1_pointer.rlp().as_hash().unwrap();
        assert_eq!(child1_hash, expected_child1_hash, "Child1 hash must match parent pointer");

        // Child hash should match computed hash
        let computed_child1_hash = child1_node.to_rlp_node().as_hash().unwrap();
        assert_eq!(child1_hash, computed_child1_hash, "Child1 hash must match computed hash");

        // Test 3: Second child hash verification
        let result = cursor.next();
        assert!(result.is_ok());
        let (key, child2_node, child2_hash) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![2; 64]));

        // Child hash should match parent's pointer
        let expected_child2_hash = child2_pointer.rlp().as_hash().unwrap();
        assert_eq!(child2_hash, expected_child2_hash, "Child2 hash must match parent pointer");

        // Child hash should match computed hash
        let computed_child2_hash = child2_node.to_rlp_node().as_hash().unwrap();
        assert_eq!(child2_hash, computed_child2_hash, "Child2 hash must match computed hash");

        // Test 4: Verify current() returns same hash
        let current_result = cursor.current();
        assert!(current_result.is_some());
        let (current_key, _current_node, current_hash) = current_result.unwrap();
        assert_eq!(current_key, &Nibbles::from_vec(vec![2; 64]));
        assert_eq!(current_hash, child2_hash, "current() should return same hash as last next()");

        // Test 5: Seek operation hash verification
        let mut new_cursor = Cursor::new_account_cursor(db.begin_ro().unwrap());
        let seek_result = new_cursor.seek(&Nibbles::from_vec(vec![1; 64]));
        assert!(seek_result.is_ok());
        let (seek_key, seek_node, seek_hash) = seek_result.unwrap().unwrap();
        assert_eq!(seek_key, &Nibbles::from_vec(vec![1; 64]));

        // Seek should return the same hash as when we traversed to this node
        assert_eq!(seek_hash, child1_hash, "Seek should return consistent hash");

        // Also verify against computed hash
        let computed_seek_hash = seek_node.to_rlp_node().as_hash().unwrap();
        assert_eq!(seek_hash, computed_seek_hash, "Seek hash must match computed hash");
    }
}
