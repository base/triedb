use std::sync::Arc;

use alloy_primitives::B256;
use alloy_trie::Nibbles;

use crate::{
    context::TransactionContext,
    location::Location,
    node::Node,
    page::{PageId, SlottedPage},
    storage::engine::StorageEngine,
};

#[derive(Debug)]
pub struct Cursor {
    storage_engine: Arc<StorageEngine>,
    context: TransactionContext,
    loc_stack: Vec<Location>,
    page_id_stack: Vec<PageId>,
    node_stack: Vec<Node>,
    key_stack: Vec<Nibbles>,
    initialized: bool,
    account_key: Option<B256>,
}

#[derive(Debug)]
pub enum CursorError {
    InvalidKey,
}

impl Cursor {
    pub fn new_account_cursor(
        storage_engine: Arc<StorageEngine>,
        context: TransactionContext,
    ) -> Self {
        Self::new_with_account_key(storage_engine, context, None)
    }

    pub fn new_storage_cursor(
        storage_engine: Arc<StorageEngine>,
        context: TransactionContext,
        account_key: B256,
    ) -> Self {
        Self::new_with_account_key(storage_engine, context, Some(account_key))
    }

    fn new_with_account_key(
        storage_engine: Arc<StorageEngine>,
        context: TransactionContext,
        account_key: Option<B256>,
    ) -> Self {
        Self {
            storage_engine,
            context,
            loc_stack: Vec::new(),
            page_id_stack: Vec::new(),
            node_stack: Vec::new(),
            key_stack: Vec::new(),
            initialized: false,
            account_key,
        }
    }

    /// Return the current key and node.
    pub fn current(&self) -> Option<(&Nibbles, &Node)> {
        self.current_key_and_node()
    }

    /// Move the cursor to the next key.
    pub fn next(&mut self) -> Result<Option<(&Nibbles, &Node)>, CursorError> {
        if !self.initialized {
            self.initialized = true;
            return self.start_from_root();
        }

        if self.key_stack.is_empty() {
            return Ok(None);
        }

        let (_, current_node) = self.current_key_and_node().unwrap();

        match current_node {
            Node::Branch { .. } => self.traverse_branch_children(),
            Node::AccountLeaf { .. } => self.backtrack_from_leaf(),
            Node::StorageLeaf { .. } => self.backtrack_from_leaf(),
        }
    }

    /// Move the cursor to the key and return a value matching or greater than the key.
    pub fn seek(&mut self, key: &Nibbles) -> Result<Option<(&Nibbles, &Node)>, CursorError> {
        println!("seek from {:?} to {:?}", self.current_key_and_node(), key);
        // If not initialized, start from root
        if !self.initialized {
            self.initialized = true;
            self.start_from_root()?;
        }

        // If we have no current position, start from root
        if self.key_stack.is_empty() {
            self.start_from_root()?;
        }

        let current_key = self.key_stack.last().unwrap();

        // If we're already at the target key, return current position
        if current_key == key {
            return Ok(self.current_key_and_node());
        }

        // Find the longest common prefix between current position and target
        let common_prefix_len = Nibbles::common_prefix_length(current_key, key);

        // Optimize: backtrack only to the point where paths diverge
        self.backtrack_to_common_ancestor(common_prefix_len)?;

        match self.current_key_and_node() {
            Some((_, node)) => {
                // Continue seeking from the common ancestor
                self.seek_recursive(key, common_prefix_len - node.prefix().len())
            }
            // If we've backtracked to empty, no higher key exists
            None => Ok(None),
        }
    }

    /// Backtrack the cursor to the common ancestor at the given prefix length
    fn backtrack_to_common_ancestor(
        &mut self,
        target_prefix_len: usize,
    ) -> Result<(), CursorError> {
        // Keep popping until we reach a key that is a prefix of the target length
        while let Some(current_key) = self.key_stack.last() {
            if current_key.len() <= target_prefix_len {
                break;
            }

            // Pop one level
            let current_loc = self.loc_stack.pop().unwrap();
            if current_loc.page_id().is_some() {
                self.page_id_stack.pop();
            }
            self.node_stack.pop();
            self.key_stack.pop();
        }

        Ok(())
    }

    /// Recursively navigate through the tree to find the target key or next higher key
    fn seek_recursive(
        &mut self,
        target_key: &Nibbles,
        path_offset: usize,
    ) -> Result<Option<(&Nibbles, &Node)>, CursorError> {
        let (current_key, current_node) = self.current_key_and_node().unwrap();

        // Compare current node's prefix with remaining target path
        let remaining_target = if path_offset < target_key.len() {
            target_key.slice(path_offset..)
        } else {
            Nibbles::default()
        };

        let common_prefix_len = std::cmp::min(current_node.prefix().len(), remaining_target.len());
        let mut matches_prefix = true;
        for i in 0..common_prefix_len {
            if current_node.prefix()[i] != remaining_target[i] {
                matches_prefix = false;
                break;
            }
        }

        // If prefix doesn't match, we need to find next higher key
        if !matches_prefix {
            return self.find_next_higher_key_from_current_level(target_key, path_offset);
        }

        // If we've matched the entire prefix
        let new_path_offset = path_offset + current_node.prefix().len();

        // If we've consumed the entire target key, this is our result
        if new_path_offset >= target_key.len() {
            println!(
                "seek_recursive {:?}: {:?}, {:?}",
                target_key, self.key_stack, self.node_stack
            );
            return Ok(self.current_key_and_node());
        }

        // Handle different node types
        match current_node {
            Node::Branch { .. } => {
                // This is a branch node, navigate to the appropriate child
                let next_nibble = target_key[new_path_offset];

                // Try to find a child at or after the target nibble
                for child_index in next_nibble..16 {
                    if let Some(child_pointer) = current_node.child(child_index).unwrap() {
                        // Load the child and continue recursion
                        self.load_child_node_into_stack(
                            child_pointer.location(),
                            current_key.clone(),
                            Some(child_index),
                        )?;
                        if child_index == next_nibble {
                            // This is the exact path we want, continue recursion
                            return self.seek_recursive(target_key, new_path_offset + 1);
                        } else {
                            // This child is higher than our target, return it
                            return Ok(self.current_key_and_node());
                        }
                    }
                }

                // No suitable child found at this level, backtrack to find next higher key
                self.backtrack_to_find_next_higher_key(target_key)
            }
            Node::AccountLeaf { .. } => self.backtrack_from_leaf(),
            Node::StorageLeaf { .. } => self.backtrack_from_leaf(),
        }
    }

    /// Find the next higher key when current node's prefix doesn't match target
    fn find_next_higher_key_from_current_level(
        &mut self,
        target_key: &Nibbles,
        _path_offset: usize,
    ) -> Result<Option<(&Nibbles, &Node)>, CursorError> {
        // Check if current key is already >= target
        if self.key_stack.last().unwrap() >= target_key {
            return Ok(self.current_key_and_node());
        }

        // Otherwise, backtrack to find next higher key
        self.backtrack_to_find_next_higher_key(target_key)
    }

    /// Backtrack through the stack to find the next higher key
    fn backtrack_to_find_next_higher_key(
        &mut self,
        target_key: &Nibbles,
    ) -> Result<Option<(&Nibbles, &Node)>, CursorError> {
        // Pop current node since it doesn't satisfy our condition
        if !self.key_stack.is_empty() {
            let current_loc = self.loc_stack.pop().unwrap();
            if current_loc.page_id().is_some() {
                self.page_id_stack.pop();
            }
            self.node_stack.pop();
            self.key_stack.pop();
        }

        // If we've backtracked to empty, no higher key exists
        if self.node_stack.is_empty() {
            return Ok(None);
        }

        let (parent_key, parent_node) = self.current_key_and_node().unwrap();

        // If this is not a branch, continue backtracking
        if !parent_node.is_branch() {
            return self.backtrack_to_find_next_higher_key(target_key);
        }

        // Find the next sibling that might contain a higher key
        let current_child_index = if parent_key.len() < target_key.len() {
            target_key[parent_key.len()]
        } else {
            15 // If we've consumed the target, look for any remaining children
        };

        // Look for the next available child after current_child_index
        for child_index in (current_child_index + 1)..16 {
            if let Some(child_pointer) = parent_node.child(child_index).unwrap() {
                self.load_child_node_into_stack(
                    child_pointer.location(),
                    parent_key.clone(),
                    Some(child_index),
                )?;
                return Ok(self.current_key_and_node());
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
    ) -> Result<(), CursorError> {
        self.loc_stack.push(child_location);

        if child_location.page_id().is_some() {
            self.page_id_stack.push(child_location.page_id().unwrap());
        }

        let child_page_id = self.page_id_stack.last().unwrap().clone();

        let child_page = self
            .storage_engine
            .get_page(&self.context, child_page_id)
            .map_err(|_| CursorError::InvalidKey)?;
        let child_slotted_page =
            SlottedPage::try_from(child_page).map_err(|_| CursorError::InvalidKey)?;

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

    /// Get the current key and node from the stack
    fn current_key_and_node(&self) -> Option<(&Nibbles, &Node)> {
        match (self.key_stack.last(), self.node_stack.last()) {
            (Some(key), Some(node)) => Some((key, node)),
            _ => None,
        }
    }

    /// Initialize cursor from root node
    fn start_from_root(&mut self) -> Result<Option<(&Nibbles, &Node)>, CursorError> {
        let root_node_page_id = self.context.root_node_page_id.unwrap();
        let root_page = self.storage_engine.get_page(&self.context, root_node_page_id).unwrap();
        let root_slotted_page = SlottedPage::try_from(root_page).unwrap();
        let root_node: Node = root_slotted_page.get_value(0).unwrap();
        let root_key = root_node.prefix().clone();

        self.loc_stack.push(Location::for_page(root_node_page_id));
        self.page_id_stack.push(root_node_page_id);
        self.node_stack.push(root_node);
        self.key_stack.push(root_key);

        if let Some(account_key) = self.account_key {
            let result = self.seek(&Nibbles::unpack(account_key))?;
            match result {
                Some((key, _)) => {
                    if key == &Nibbles::unpack(account_key) {
                        self.initialize_storage_stacks()?;
                        println!("initialize_storage_stacks {:?}", self);
                        return Ok(self.current_key_and_node());
                    } else {
                        self.initialize_storage_stacks()?;
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
        Ok(Some((key_ref, node_ref)))
    }

    fn initialize_storage_stacks(&mut self) -> Result<(), CursorError> {
        let (current_key, current_node) = self.current_key_and_node().unwrap();
        let storage_root = current_node.direct_child().unwrap();
        if storage_root.is_none() {
            self.loc_stack.clear();
            self.page_id_stack.clear();
            self.node_stack.clear();
            self.key_stack.clear();
            return Ok(());
        }

        let storage_root_pointer = storage_root.unwrap();
        self.load_child_node_into_stack(
            storage_root_pointer.location(),
            current_key.clone(),
            None,
        )?;

        let storage_root_loc = self.loc_stack.pop().unwrap();
        self.loc_stack.clear();
        self.loc_stack.push(storage_root_loc);

        let storage_root_page_id = self.page_id_stack.pop().unwrap();
        self.page_id_stack.clear();
        self.page_id_stack.push(storage_root_page_id);

        let storage_root_node = self.node_stack.pop().unwrap();
        let storage_root_key = storage_root_node.prefix().clone();

        self.node_stack.clear();
        self.node_stack.push(storage_root_node);

        self.key_stack.clear();
        self.key_stack.push(storage_root_key);

        Ok(())
    }

    /// Traverse children of a branch node
    fn traverse_branch_children(&mut self) -> Result<Option<(&Nibbles, &Node)>, CursorError> {
        let (parent_key, parent_node) = self.current_key_and_node().unwrap();

        for child_index in 0..16 {
            let child = parent_node.child(child_index).unwrap();
            if child.is_none() {
                continue;
            }

            let child_pointer = child.as_ref().unwrap();
            self.load_child_node_into_stack(
                child_pointer.location(),
                parent_key.clone(),
                Some(child_index as u8),
            )?;
            return Ok(self.current_key_and_node());
        }

        // No children found, backtrack
        self.backtrack_to_next_sibling()
    }

    /// Backtrack to find the next sibling at any level
    fn backtrack_to_next_sibling(&mut self) -> Result<Option<(&Nibbles, &Node)>, CursorError> {
        while !self.node_stack.is_empty() {
            // Pop current node
            let current_loc = self.loc_stack.pop().unwrap();
            if current_loc.page_id().is_some() {
                self.page_id_stack.pop();
            }
            self.node_stack.pop();
            let current_key = self.key_stack.pop().unwrap();

            // If we've reached the root, we're done
            if self.node_stack.is_empty() {
                return Ok(None);
            }

            let parent_key = self.key_stack.last().unwrap().clone();

            // Get current child index and try to find next sibling
            let current_child_index = current_key.get(parent_key.len()).unwrap();

            if self.find_next_sibling_from_index(current_child_index + 1)? {
                return Ok(self.current_key_and_node());
            }

            // No sibling found, continue backtracking
        }

        Ok(None)
    }

    /// Find the next sibling starting from the given index
    fn find_next_sibling_from_index(&mut self, start_index: u8) -> Result<bool, CursorError> {
        let (parent_key, parent_node) = self.current_key_and_node().unwrap();
        let children = match parent_node {
            Node::Branch { children, .. } => children,
            _ => return Ok(false),
        };

        for child_index in start_index..16 {
            if children[child_index as usize].is_none() {
                continue;
            }

            let child_pointer = children[child_index as usize].as_ref().unwrap();
            self.load_child_node_into_stack(
                child_pointer.location(),
                parent_key.clone(),
                Some(child_index as u8),
            )?;
            return Ok(true);
        }

        Ok(false)
    }

    /// Backtrack from a leaf node
    fn backtrack_from_leaf(&mut self) -> Result<Option<(&Nibbles, &Node)>, CursorError> {
        // Pop current leaf node from stacks
        let current_loc = self.loc_stack.pop().unwrap();
        if current_loc.page_id().is_some() {
            self.page_id_stack.pop();
        }
        self.node_stack.pop();
        let mut child_key = self.key_stack.pop().unwrap();

        // Now continue backtracking until we find a parent with a next sibling
        while !self.node_stack.is_empty() {
            let parent_key = self.key_stack.last().unwrap();

            // Get the current child index from the child_key
            let current_child_index = child_key.get(parent_key.len()).unwrap();

            // Try to find the next sibling
            if self.find_next_sibling_from_index(current_child_index + 1)? {
                return Ok(self.current_key_and_node());
            }

            // No sibling found at this level, backtrack further
            let current_loc = self.loc_stack.pop().unwrap();
            if current_loc.page_id().is_some() {
                self.page_id_stack.pop();
            }
            self.node_stack.pop();
            child_key = self.key_stack.pop().unwrap();
        }

        // Reached root with no more siblings
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::{Address, B256, U256};

    use crate::{
        node::TrieValue,
        path::{AddressPath, StoragePath},
        storage::test_utils::{create_test_account, create_test_engine},
    };

    use super::*;

    #[test]
    fn test_account_cursor() {
        let (storage_engine, mut context) = create_test_engine(100);

        // top branch has 2 children, one is a leaf and the other is a branch with 2 children

        let address_path1 = AddressPath::new(Nibbles::from_vec(vec![1; 64]));
        let account1 = create_test_account(1, 1);

        let address_path2 = AddressPath::new(Nibbles::from_vec(vec![2; 64]));
        let account2 = create_test_account(2, 2);

        let addr2_storage1 =
            StoragePath::for_address_path_and_slot(address_path2.clone(), B256::from([0x01; 32]));

        let address_path3 = AddressPath::new(Nibbles::from_vec(
            vec![2, 2].into_iter().chain(vec![3; 62]).collect::<Vec<_>>(),
        ));
        let account3 = create_test_account(3, 3);

        storage_engine
            .set_values(
                &mut context,
                vec![
                    (address_path1.clone().into(), Some(account1.clone().into())),
                    (address_path2.clone().into(), Some(account2.clone().into())),
                    (addr2_storage1.clone().into(), Some(U256::from(123).into())),
                    (address_path3.clone().into(), Some(account3.clone().into())),
                ]
                .as_mut(),
            )
            .unwrap();

        let mut cursor = Cursor::new_account_cursor(Arc::new(storage_engine), context);

        // first item found is the root node (branch)
        let result = cursor.next();
        let (key, branch_node) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::default());
        assert_eq!(branch_node.prefix(), &Nibbles::default());
        assert!(branch_node.child(1).unwrap().is_some());
        assert!(branch_node.child(2).unwrap().is_some());

        // second item found is the first account leaf node
        let result = cursor.next();
        let (key, leaf_node) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![1; 64]));
        assert_eq!(leaf_node.prefix(), &Nibbles::from_vec(vec![1; 63]));
        assert!(matches!(leaf_node, Node::AccountLeaf { .. }));

        // current also returns the first account leaf node
        let result = cursor.current();
        assert!(result.is_some());
        let (key, leaf_node) = result.unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![1; 64]));
        assert_eq!(leaf_node.prefix(), &Nibbles::from_vec(vec![1; 63]));
        assert!(matches!(leaf_node, Node::AccountLeaf { .. }));

        // next item found is the nested branch node
        let result = cursor.next();
        let (key, branch_node) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![2, 2]));
        assert_eq!(branch_node.prefix(), &Nibbles::from_vec(vec![2]));
        assert!(branch_node.child(2).unwrap().is_some());
        assert!(branch_node.child(3).unwrap().is_some());

        // next item found is the second account leaf node
        let result = cursor.next();
        let (key, leaf_node) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![2; 64]));
        assert_eq!(leaf_node.prefix(), &Nibbles::from_vec(vec![2; 61]));
        assert!(matches!(leaf_node, Node::AccountLeaf { .. }));

        // next item found is the third account leaf node (skipping the second account's storage)
        let result = cursor.next();
        let (key, leaf_node) = result.unwrap().unwrap();
        assert_eq!(
            key,
            &Nibbles::from_vec(vec![2, 2].into_iter().chain(vec![3; 62]).collect::<Vec<_>>())
        );
        assert_eq!(leaf_node.prefix(), &Nibbles::from_vec(vec![3; 61]));
        assert!(matches!(leaf_node, Node::AccountLeaf { .. }));

        // no more account trie nodes found
        let result = cursor.next();
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_storage_cursor() {
        let (storage_engine, mut context) = create_test_engine(300);

        // Create an account
        let address = Address::from([0x42; 20]);
        let account = create_test_account(100, 1);
        let account_path = AddressPath::for_address(address);

        // Create storage slots for the account
        let storage_key1 = B256::from([0x01; 32]);
        let storage_value1 = U256::from(0x1111);
        let storage_path1 = StoragePath::for_address_and_slot(address, storage_key1);

        let storage_key2 = B256::from([0x02; 32]);
        let storage_value2 = U256::from(0x2222);
        let storage_path2 = StoragePath::for_address_and_slot(address, storage_key2);

        // Set account and storage values
        storage_engine
            .set_values(
                &mut context,
                vec![
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.into(), Some(TrieValue::Storage(storage_value1))),
                    (storage_path2.into(), Some(TrieValue::Storage(storage_value2))),
                ]
                .as_mut(),
            )
            .unwrap();

        let mut cursor =
            Cursor::new_storage_cursor(Arc::new(storage_engine), context, account_path.into());

        // Iterate through all nodes and count what we find
        let mut found_account = false;
        let mut found_storage_nodes = 0;
        let mut found_nodes = 0;

        while let Ok(Some((key, node))) = cursor.next() {
            found_nodes += 1;
            match node {
                Node::AccountLeaf { .. } => {
                    found_account = true;
                }
                Node::StorageLeaf { .. } => {
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
        let (storage_engine, mut context) = create_test_engine(100);

        // Create an account
        let address = Address::from([0x42; 20]);
        let account = create_test_account(100, 1);
        let account_path = AddressPath::for_address(address);

        // Set account and storage values
        storage_engine
            .set_values(
                &mut context,
                vec![
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                ]
                .as_mut(),
            )
            .unwrap();

        let mut cursor =
            Cursor::new_storage_cursor(Arc::new(storage_engine), context.clone(), account_path.into());

        let result = cursor.next();
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());

        let mut cursor = Cursor::new_storage_cursor(cursor.storage_engine.clone(), context, B256::from([0x00; 32]));
        let result = cursor.next();
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_account_cursor_seek() {
        let (storage_engine, mut context) = create_test_engine(100);

        // Create accounts with different patterns to test nearby seeking
        let accounts = vec![
            (vec![1, 0], create_test_account(1, 1)),
            (vec![1, 5], create_test_account(2, 2)),
            (vec![2, 0], create_test_account(3, 3)),
            (vec![2, 5], create_test_account(4, 4)),
            (vec![3, 0], create_test_account(5, 5)),
        ];

        for (path_vec, account) in &accounts {
            // Pad to 64 nibbles for AddressPath
            let mut full_path = path_vec.clone();
            full_path.extend(vec![0; 62]);
            let path = AddressPath::new(Nibbles::from_vec(full_path));
            storage_engine
                .set_values(
                    &mut context,
                    vec![
                        (path.clone().into(), Some(account.clone().into())),
                        (
                            StoragePath::for_address_path_and_slot(
                                path.clone(),
                                B256::from([0x01; 32]),
                            )
                            .into(),
                            Some(U256::from(123).into()),
                        ),
                    ]
                    .as_mut(),
                )
                .unwrap();
        }

        let mut cursor = Cursor::new_account_cursor(Arc::new(storage_engine), context);

        // First, position the cursor at [1, 0, 0, 0, ...]
        let mut target1 = vec![1, 0];
        target1.extend(vec![0; 62]);
        let result = cursor.seek(&Nibbles::from_vec(target1.clone()));
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(target1));

        // Now seek to a nearby key [1, 3] - should efficiently find [1, 5, ...]
        // This should reuse the common prefix [1] and not go back to root
        let target2 = vec![1, 3];
        let mut expected2 = vec![1, 5];
        expected2.extend(vec![0; 62]);
        let result = cursor.seek(&Nibbles::from_vec(target2));
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(expected2));

        // Now move to the next key, which should be the branch at [2]
        let result = cursor.next();
        let (key, branch_node) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(vec![2]));
        assert_eq!(branch_node.prefix(), &Nibbles::default()); // Branch prefix should be empty
        assert!(branch_node.child(0).unwrap().is_some());
        assert!(branch_node.child(5).unwrap().is_some());

        // Seek to another nearby key [2, 3, ...] - should find [2, 5, ...]
        let mut target3 = vec![2, 3];
        target3.extend(vec![0; 62]);
        let mut expected3 = vec![2, 5];
        expected3.extend(vec![0; 62]);
        let result = cursor.seek(&Nibbles::from_vec(target3));
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(expected3.clone()));

        // Seek backwards to a key we've already passed
        let mut target4 = vec![2, 0];
        target4.extend(vec![0; 62]);
        let mut expected4 = vec![2, 0];
        expected4.extend(vec![0; 62]);
        let result = cursor.seek(&Nibbles::from_vec(target4));
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(expected4.clone()));

        // Seek to exact current position - should return immediately
        let result = cursor.seek(&Nibbles::from_vec(expected4.clone()));
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(expected4));

        // Next should be [2, 5, ...]
        let mut expected3 = vec![2, 5];
        expected3.extend(vec![0; 62]);
        let result = cursor.next();
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(expected3));

        // Next should be [3, 0, ...]
        let mut expected = vec![3];
        expected.extend(vec![0; 63]);
        let result = cursor.next();
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, &Nibbles::from_vec(expected));

        // Next should be empty
        let result = cursor.next();
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_storage_cursor_seek() {
        use crate::{node::TrieValue, path::StoragePath};
        use alloy_primitives::{Address, B256, U256};

        let (storage_engine, mut context) = create_test_engine(300);

        // Create an account with storage
        let address = Address::from([0x42; 20]);
        let account = create_test_account(100, 1);
        let account_path = AddressPath::for_address(address);

        // Create storage slots
        let storage_key1 = B256::from([0x01; 32]);
        let storage_value1 = U256::from(0x1111);
        let storage_path1 = StoragePath::for_address_and_slot(address, storage_key1);

        let storage_key2 = B256::from([0x05; 32]);
        let storage_value2 = U256::from(0x2222);
        let storage_path2 = StoragePath::for_address_and_slot(address, storage_key2);

        // Set account and storage values
        storage_engine
            .set_values(
                &mut context,
                vec![
                    (account_path.clone().into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.full_path(), Some(TrieValue::Storage(storage_value1))),
                    (storage_path2.full_path(), Some(TrieValue::Storage(storage_value2))),
                ]
                .as_mut(),
            )
            .unwrap();

        let mut cursor = Cursor::new_storage_cursor(
            Arc::new(storage_engine),
            context,
            account_path.clone().into(),
        );

        // Seek to an empty path (should find the root branch)
        let result = cursor.seek(&Nibbles::default());
        assert!(result.is_ok());
        let result = result.unwrap();
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, &Nibbles::default());
        assert!(matches!(result.unwrap().1, Node::Branch { .. }));

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
}
