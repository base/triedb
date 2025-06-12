use alloy_trie::Nibbles;

use crate::{
    context::TransactionContext, location::Location, node::Node, page::SlottedPage,
    storage::engine::StorageEngine,
};

#[derive(Debug)]
pub struct Cursor<'c> {
    storage_engine: StorageEngine,
    context: TransactionContext,
    loc_stack: Vec<Location>,
    page_stack: Vec<SlottedPage<'c>>,
    node_stack: Vec<Node>,
    key_stack: Vec<Nibbles>,
    initialized: bool,
}

#[derive(Debug)]
pub enum CursorError {
    InvalidKey,
}

impl<'c> Cursor<'c> {
    pub fn new(storage_engine: StorageEngine, context: TransactionContext) -> Self {
        Self {
            storage_engine,
            context,
            loc_stack: Vec::new(),
            page_stack: Vec::new(),
            node_stack: Vec::new(),
            key_stack: Vec::new(),
            initialized: false,
        }
    }

    /// Move the cursor to the key and return a value matching or greater than the key.
    pub fn seek(&mut self, key: Nibbles) -> Result<Option<(Nibbles, Node)>, CursorError> {
        // If not initialized, start from root
        if !self.initialized {
            self.initialized = true;
            return self.seek_from_root(&key);
        }

        // If we have no current position, start from root
        if self.key_stack.is_empty() {
            return self.seek_from_root(&key);
        }

        let current_key = self.key_stack.last().unwrap();

        // If we're already at the target key, return current position
        if current_key == &key {
            let current_node = self.node_stack.last().unwrap().clone();
            return Ok(Some((current_key.clone(), current_node)));
        }

        // Find the longest common prefix between current position and target
        let common_prefix_len = Nibbles::common_prefix_length(current_key, &key);

        // If keys are completely different, start from root
        if common_prefix_len == 0 {
            return self.seek_from_root(&key);
        }

        // Optimize: backtrack only to the point where paths diverge
        self.backtrack_to_common_ancestor(common_prefix_len)?;

        // Continue seeking from the common ancestor
        self.seek_from_current_position(&key)
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
                self.page_stack.pop();
            }
            self.node_stack.pop();
            self.key_stack.pop();
        }
        Ok(())
    }

    /// Seek from the current cursor position (optimized for nearby targets)
    fn seek_from_current_position(
        &mut self,
        target_key: &Nibbles,
    ) -> Result<Option<(Nibbles, Node)>, CursorError> {
        let current_key = self.key_stack.last().unwrap().clone();
        let current_node = self.node_stack.last().unwrap().clone();

        // If we've reached or passed the target, return current position
        if current_key >= *target_key {
            return Ok(Some((current_key, current_node)));
        }

        // If this is not a branch node, we need to backtrack to find next higher key
        if !current_node.is_branch() {
            return self.backtrack_to_find_next_higher_key(target_key);
        }

        // This is a branch node - find the appropriate child for the target
        let path_offset = current_key.len();

        if path_offset >= target_key.len() {
            // We've consumed the entire target key - current position is the result
            return Ok(Some((current_key, current_node)));
        }

        let target_nibble = target_key[path_offset];

        // Look for a child at or after the target nibble
        for child_index in target_nibble..16 {
            if let Some(child_pointer) = current_node.child(child_index).unwrap() {
                let child_node = self.load_child_node(child_pointer.location())?;
                let child_key = self.build_child_key(&current_key, child_index, &child_node);

                self.key_stack.push(child_key.clone());

                if child_index == target_nibble {
                    // This is the exact path we want, continue recursively
                    return self.seek_from_current_position(target_key);
                } else {
                    // This child is higher than our target, return it
                    return Ok(Some((child_key, child_node)));
                }
            }
        }

        // No suitable child found, backtrack to find next higher key
        self.backtrack_to_find_next_higher_key(target_key)
    }

    /// Fallback: seek starting from the root (used when optimization isn't possible)
    fn seek_from_root(&mut self, key: &Nibbles) -> Result<Option<(Nibbles, Node)>, CursorError> {
        // Clear existing state to start fresh
        self.loc_stack.clear();
        self.page_stack.clear();
        self.node_stack.clear();
        self.key_stack.clear();

        // Start from root
        let root_node_page_id = match self.context.root_node_page_id {
            Some(id) => id,
            None => return Ok(None),
        };

        let root_page = self.storage_engine.get_page(&self.context, root_node_page_id).unwrap();
        let root_slotted_page = SlottedPage::try_from(root_page).unwrap();
        let root_node: Node = root_slotted_page.get_value(0).unwrap();

        self.loc_stack.push(Location::for_page(root_node_page_id));
        self.page_stack.push(root_slotted_page);
        self.node_stack.push(root_node.clone());
        self.key_stack.push(Nibbles::default());

        // Navigate through the tree to find the target key or next higher key
        self.seek_recursive(key, 0)
    }

    /// Recursively navigate through the tree to find the target key or next higher key
    fn seek_recursive(
        &mut self,
        target_key: &Nibbles,
        path_offset: usize,
    ) -> Result<Option<(Nibbles, Node)>, CursorError> {
        let current_node = self.node_stack.last().unwrap().clone();
        let current_key = self.key_stack.last().unwrap().clone();

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
            return Ok(Some((current_key, current_node)));
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
                        let child_node = self.load_child_node(child_pointer.location())?;
                        let child_key =
                            self.build_child_key(&current_key, child_index, &child_node);

                        self.key_stack.push(child_key.clone());

                        if child_index == next_nibble {
                            // This is the exact path we want, continue recursion
                            return self.seek_recursive(target_key, new_path_offset + 1);
                        } else {
                            // This child is higher than our target, return it
                            return Ok(Some((child_key, child_node)));
                        }
                    }
                }

                // No suitable child found at this level, backtrack to find next higher key
                self.backtrack_to_find_next_higher_key(target_key)
            }
            Node::AccountLeaf { storage_root, .. } => {
                // If there's still remaining path and this account has storage, traverse into
                // storage
                if new_path_offset < target_key.len() {
                    if let Some(storage_pointer) = storage_root {
                        let storage_node = self.load_child_node(storage_pointer.location())?;
                        // For storage, treat it like a child at index 0 for key building
                        let storage_key = self.build_child_key(&current_key, 0, &storage_node);

                        self.key_stack.push(storage_key);
                        return self.seek_recursive(target_key, new_path_offset);
                    }
                }

                // No storage or we've consumed the target, find next higher key
                self.find_next_higher_key_from_current_level(target_key, path_offset)
            }
            Node::StorageLeaf { .. } => {
                // Storage leaf with remaining path, find next higher key
                self.find_next_higher_key_from_current_level(target_key, path_offset)
            }
        }
    }

    /// Find the next higher key when current node's prefix doesn't match target
    fn find_next_higher_key_from_current_level(
        &mut self,
        target_key: &Nibbles,
        _path_offset: usize,
    ) -> Result<Option<(Nibbles, Node)>, CursorError> {
        let current_node = self.node_stack.last().unwrap().clone();
        let current_key = self.key_stack.last().unwrap().clone();

        // If current key is already >= target, return it
        if current_key >= *target_key {
            return Ok(Some((current_key, current_node)));
        }

        // Otherwise, backtrack to find next higher key
        self.backtrack_to_find_next_higher_key(target_key)
    }

    /// Backtrack through the stack to find the next higher key
    fn backtrack_to_find_next_higher_key(
        &mut self,
        target_key: &Nibbles,
    ) -> Result<Option<(Nibbles, Node)>, CursorError> {
        // Pop current node since it doesn't satisfy our condition
        if !self.key_stack.is_empty() {
            let current_loc = self.loc_stack.pop().unwrap();
            if current_loc.page_id().is_some() {
                self.page_stack.pop();
            }
            self.node_stack.pop();
            self.key_stack.pop();
        }

        // If we've backtracked to empty, no higher key exists
        if self.node_stack.is_empty() {
            return Ok(None);
        }

        let parent_node = self.node_stack.last().unwrap().clone();
        let parent_key = self.key_stack.last().unwrap().clone();

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
                let child_node = self.load_child_node(child_pointer.location())?;
                let child_key = self.build_child_key(&parent_key, child_index, &child_node);

                self.key_stack.push(child_key.clone());
                return Ok(Some((child_key, child_node)));
            }
        }

        // No suitable sibling found, continue backtracking
        self.backtrack_to_find_next_higher_key(target_key)
    }

    /// Load a child node from either the same page or a different page
    fn load_child_node(&mut self, child_location: Location) -> Result<Node, CursorError> {
        self.loc_stack.push(child_location);

        let child_node = if child_location.page_id().is_some() {
            let child_page = self
                .storage_engine
                .get_page(&self.context, child_location.page_id().unwrap())
                .map_err(|_| CursorError::InvalidKey)?;
            let child_slotted_page =
                SlottedPage::try_from(child_page).map_err(|_| CursorError::InvalidKey)?;
            let child_node: Node =
                child_slotted_page.get_value(0).map_err(|_| CursorError::InvalidKey)?;

            self.page_stack.push(child_slotted_page);
            self.node_stack.push(child_node.clone());
            child_node
        } else {
            let child_node: Node = self
                .page_stack
                .last()
                .unwrap()
                .get_value(child_location.cell_index().unwrap())
                .map_err(|_| CursorError::InvalidKey)?;

            self.node_stack.push(child_node.clone());
            child_node
        };

        Ok(child_node)
    }

    /// Build the full key for a child node
    fn build_child_key(&self, base_key: &Nibbles, child_index: u8, child_node: &Node) -> Nibbles {
        let mut child_key = base_key.clone();
        child_key.push(child_index);
        child_key.extend_from_slice(child_node.prefix());
        child_key
    }

    /// Get the current entry.
    fn current(&mut self) -> Result<Option<Nibbles>, CursorError> {
        let key = self.key_stack.last().cloned();
        match key {
            Some(key) => Ok(Some(key)),
            None => Ok(None),
        }
    }

    /// Move the cursor to the next key.
    fn next(&mut self) -> Result<Option<(Nibbles, Node)>, CursorError> {
        if !self.initialized {
            self.initialized = true;
            return self.start_from_root();
        }

        if self.key_stack.is_empty() {
            return Ok(None);
        }

        let current_node = self.node_stack.last().unwrap();
        match current_node {
            Node::Branch { .. } => self.traverse_branch_children(),
            Node::AccountLeaf { storage_root, .. } => {
                // If account has storage, traverse into storage subtrie first
                if let Some(storage_pointer) = storage_root {
                    let storage_node = self.load_child_node(storage_pointer.location())?;
                    let current_key = self.key_stack.last().unwrap().clone();

                    // For storage traversal, we need to handle it like a child traversal
                    let mut storage_key = current_key.clone();
                    storage_key.extend_from_slice(storage_node.prefix());

                    self.key_stack.push(storage_key.clone());
                    return Ok(Some((storage_key, storage_node)));
                } else {
                    // No storage, backtrack to find next account
                    self.backtrack_from_leaf()
                }
            }
            Node::StorageLeaf { .. } => self.backtrack_from_leaf(),
        }
    }

    /// Initialize cursor from root node
    fn start_from_root(&mut self) -> Result<Option<(Nibbles, Node)>, CursorError> {
        let root_node_page_id = self.context.root_node_page_id.unwrap();
        let root_page = self.storage_engine.get_page(&self.context, root_node_page_id).unwrap();
        let root_slotted_page = SlottedPage::try_from(root_page).unwrap();
        let root_node: Node = root_slotted_page.get_value(0).unwrap();
        let root_key = root_node.prefix();

        self.loc_stack.push(Location::for_page(root_node_page_id));
        self.page_stack.push(root_slotted_page);
        self.node_stack.push(root_node.clone());
        self.key_stack.push(root_key.clone());

        Ok(Some((root_key.clone(), root_node)))
    }

    /// Traverse children of a branch node
    fn traverse_branch_children(&mut self) -> Result<Option<(Nibbles, Node)>, CursorError> {
        let current_node = self.node_stack.last().unwrap();
        let current_key = self.key_stack.last().unwrap();
        let base_child_key = current_key.clone();

        for child_index in 0..16 {
            let child = current_node.child(child_index).unwrap();
            if child.is_none() {
                continue;
            }

            let child_pointer = child.as_ref().unwrap();
            let child_node = self.load_child_node(child_pointer.location())?;
            let child_key = self.build_child_key(&base_child_key, child_index as u8, &child_node);

            self.key_stack.push(child_key.clone());
            return Ok(Some((child_key, child_node)));
        }

        // No children found, backtrack
        self.backtrack_to_next_sibling()
    }

    /// Backtrack to find the next sibling at any level
    fn backtrack_to_next_sibling(&mut self) -> Result<Option<(Nibbles, Node)>, CursorError> {
        while !self.node_stack.is_empty() {
            // Pop current node
            let current_loc = self.loc_stack.pop().unwrap();
            if current_loc.page_id().is_some() {
                self.page_stack.pop();
            }
            self.node_stack.pop();
            let current_key = self.key_stack.pop().unwrap();

            // If we've reached the root, we're done
            if self.node_stack.is_empty() {
                return Ok(None);
            }
            let parent_node = self.node_stack.last().unwrap().clone();
            if matches!(parent_node, Node::AccountLeaf { .. }) {
                // If we've reached an account leaf, we need to backtrack to its parent
                continue;
            }

            let parent_key = self.key_stack.last().unwrap().clone();

            // Get current child index and try to find next sibling
            let current_child_index = current_key.get(parent_key.len()).unwrap();

            if let Some(result) = self.find_next_sibling_from_index(
                current_child_index + 1,
                &parent_node,
                &parent_key,
            )? {
                return Ok(Some(result));
            }

            // No sibling found, continue backtracking
        }

        Ok(None)
    }

    /// Find the next sibling starting from the given index
    fn find_next_sibling_from_index(
        &mut self,
        start_index: u8,
        parent_node: &Node,
        parent_key: &Nibbles,
    ) -> Result<Option<(Nibbles, Node)>, CursorError> {
        let children = match parent_node {
            Node::Branch { children, .. } => children,
            _ => return Ok(None),
        };

        for child_index in start_index..16 {
            if children[child_index as usize].is_none() {
                continue;
            }

            let child_pointer = children[child_index as usize].as_ref().unwrap();
            let child_node = self.load_child_node(child_pointer.location())?;
            let child_key = self.build_child_key(&parent_key, child_index, &child_node);

            self.key_stack.push(child_key.clone());
            return Ok(Some((child_key, child_node)));
        }

        Ok(None)
    }

    /// Backtrack from a leaf node
    fn backtrack_from_leaf(&mut self) -> Result<Option<(Nibbles, Node)>, CursorError> {
        // Pop current leaf node from stacks
        let current_loc = self.loc_stack.pop().unwrap();
        if current_loc.page_id().is_some() {
            self.page_stack.pop();
        }
        self.node_stack.pop();
        let mut child_key = self.key_stack.pop().unwrap();

        // Now continue backtracking until we find a parent with a next sibling
        while !self.node_stack.is_empty() {
            let parent_node = self.node_stack.last().unwrap().clone();

            // If we've reached an account leaf, we need to backtrack to its parent
            if !matches!(parent_node, Node::AccountLeaf { .. }) {
                let parent_key = self.key_stack.last().unwrap().clone();

                // Get the current child index from the child_key
                let current_child_index = child_key.get(parent_key.len()).unwrap();

                // Try to find the next sibling
                if let Some(result) = self.find_next_sibling_from_index(
                    current_child_index + 1,
                    &parent_node,
                    &parent_key,
                )? {
                    return Ok(Some(result));
                }
            }

            // No sibling found at this level, backtrack further
            let current_loc = self.loc_stack.pop().unwrap();
            if current_loc.page_id().is_some() {
                self.page_stack.pop();
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
    use crate::{
        path::AddressPath,
        storage::test_utils::{create_test_account, create_test_engine},
    };

    use super::*;

    #[test]
    fn test_cursor() {
        let (mut storage_engine, mut context) = create_test_engine(100);

        // top branch has 2 children, one is a leaf and the other is a branch with 2 children

        let path1 = AddressPath::new(Nibbles::from_vec(vec![1; 64]));
        let account1 = create_test_account(1, 1);

        let path2 = AddressPath::new(Nibbles::from_vec(vec![2; 64]));
        let account2 = create_test_account(2, 2);

        let path3 = AddressPath::new(Nibbles::from_vec(
            vec![2, 2].into_iter().chain(vec![3; 62]).collect::<Vec<_>>(),
        ));
        let account3 = create_test_account(3, 3);

        storage_engine
            .set_values(
                &mut context,
                vec![
                    (path1.clone().into(), Some(account1.clone().into())),
                    (path2.clone().into(), Some(account2.clone().into())),
                    (path3.clone().into(), Some(account3.clone().into())),
                ]
                .as_mut(),
            )
            .unwrap();

        let mut cursor = Cursor::new(storage_engine, context);
        let result = cursor.next();
        let (key, branch_node) = result.unwrap().unwrap();
        assert_eq!(key, Nibbles::default());
        assert_eq!(branch_node.prefix(), &Nibbles::default());
        assert!(branch_node.child(1).unwrap().is_some());
        assert!(branch_node.child(2).unwrap().is_some());

        let result = cursor.next();
        let (key, leaf_node) = result.unwrap().unwrap();
        assert_eq!(key, Nibbles::from_vec(vec![1; 64]));
        assert_eq!(leaf_node.prefix(), &Nibbles::from_vec(vec![1; 63]));
        assert!(matches!(leaf_node, Node::AccountLeaf { .. }));

        let result = cursor.next();
        let (key, branch_node) = result.unwrap().unwrap();
        assert_eq!(key, Nibbles::from_vec(vec![2, 2]));
        assert_eq!(branch_node.prefix(), &Nibbles::from_vec(vec![2]));
        assert!(branch_node.child(2).unwrap().is_some());
        assert!(branch_node.child(3).unwrap().is_some());

        let result = cursor.next();
        let (key, leaf_node) = result.unwrap().unwrap();
        assert_eq!(key, Nibbles::from_vec(vec![2; 64]));
        assert_eq!(leaf_node.prefix(), &Nibbles::from_vec(vec![2; 61]));
        assert!(matches!(leaf_node, Node::AccountLeaf { .. }));

        let result = cursor.next();
        let (key, leaf_node) = result.unwrap().unwrap();
        assert_eq!(
            key,
            Nibbles::from_vec(vec![2, 2].into_iter().chain(vec![3; 62]).collect::<Vec<_>>())
        );
        assert_eq!(leaf_node.prefix(), &Nibbles::from_vec(vec![3; 61]));
        assert!(matches!(leaf_node, Node::AccountLeaf { .. }));

        let result = cursor.next();
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_cursor_with_storage() {
        use crate::{node::TrieValue, path::StoragePath};
        use alloy_primitives::{Address, B256, U256};

        let (mut storage_engine, mut context) = create_test_engine(300);

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
                    (account_path.into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.into(), Some(TrieValue::Storage(storage_value1))),
                    (storage_path2.into(), Some(TrieValue::Storage(storage_value2))),
                ]
                .as_mut(),
            )
            .unwrap();

        let mut cursor = Cursor::new(storage_engine, context);

        // Iterate through all nodes and count what we find
        let mut found_account = false;
        let mut found_storage_nodes = 0;

        while let Ok(Some((key, node))) = cursor.next() {
            match node {
                Node::AccountLeaf { .. } => {
                    assert_eq!(key.len(), 64);
                    found_account = true;
                }
                Node::StorageLeaf { .. } => {
                    assert_eq!(key.len(), 128);
                    found_storage_nodes += 1;
                }
                _ => {}
            }
        }

        // We should have found the account and storage entries
        assert!(found_account, "Should have found the account node");
        assert!(found_storage_nodes > 0, "Should have found storage nodes");
    }

    #[test]
    fn test_cursor_seek() {
        let (mut storage_engine, mut context) = create_test_engine(100);

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
                    vec![(path.into(), Some(account.clone().into()))].as_mut(),
                )
                .unwrap();
        }

        let mut cursor = Cursor::new(storage_engine, context);

        // First, position the cursor at [1, 0, 0, 0, ...]
        let mut target1 = vec![1, 0];
        target1.extend(vec![0; 62]);
        let result = cursor.seek(Nibbles::from_vec(target1.clone()));
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, Nibbles::from_vec(target1));

        // Now seek to a nearby key [1, 3] - should efficiently find [1, 5, ...]
        // This should reuse the common prefix [1] and not go back to root
        let target2 = vec![1, 3];
        let mut expected2 = vec![1, 5];
        expected2.extend(vec![0; 62]);
        let result = cursor.seek(Nibbles::from_vec(target2));
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, Nibbles::from_vec(expected2));

        // Now move to the next key, which should be the branch at [2]
        let result = cursor.next();
        let (key, branch_node) = result.unwrap().unwrap();
        assert_eq!(key, Nibbles::from_vec(vec![2]));
        assert_eq!(branch_node.prefix(), &Nibbles::default()); // Branch prefix should be empty
        assert!(branch_node.child(0).unwrap().is_some());
        assert!(branch_node.child(5).unwrap().is_some());

        // Seek to another nearby key [2, 3, ...] - should find [2, 5, ...]
        let mut target3 = vec![2, 3];
        target3.extend(vec![0; 62]);
        let mut expected3 = vec![2, 5];
        expected3.extend(vec![0; 62]);
        let result = cursor.seek(Nibbles::from_vec(target3));
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, Nibbles::from_vec(expected3.clone()));

        // Seek backwards to a key we've already passed
        let mut target4 = vec![2, 0];
        target4.extend(vec![0; 62]);
        let mut expected4 = vec![2, 0];
        expected4.extend(vec![0; 62]);
        let result = cursor.seek(Nibbles::from_vec(target4));
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, Nibbles::from_vec(expected4.clone()));

        // Seek to exact current position - should return immediately
        let result = cursor.seek(Nibbles::from_vec(expected4.clone()));
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, Nibbles::from_vec(expected4));

        // Next should be [2, 5, ...]
        let mut expected3 = vec![2, 5];
        expected3.extend(vec![0; 62]);
        let result = cursor.next();
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, Nibbles::from_vec(expected3));

        // Next should be [3, 0, ...]
        let mut expected = vec![3];
        expected.extend(vec![0; 63]);
        let result = cursor.next();
        let (key, _) = result.unwrap().unwrap();
        assert_eq!(key, Nibbles::from_vec(expected));

        // Next should be empty
        let result = cursor.next();
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_cursor_seek_storage() {
        use crate::{node::TrieValue, path::StoragePath};
        use alloy_primitives::{Address, B256, U256};

        let (mut storage_engine, mut context) = create_test_engine(300);

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
                    (account_path.into(), Some(TrieValue::Account(account.clone()))),
                    (storage_path1.full_path(), Some(TrieValue::Storage(storage_value1))),
                    (storage_path2.full_path(), Some(TrieValue::Storage(storage_value2))),
                ]
                .as_mut(),
            )
            .unwrap();

        let mut cursor = Cursor::new(storage_engine, context);

        // Seek to the first storage slot
        let result = cursor.seek(storage_path1.full_path());
        assert!(result.is_ok());
        let result = result.unwrap();
        assert!(result.is_some());

        // Seek to a storage slot that doesn't exist (should find next higher)
        let missing_storage_key = B256::from([0x03; 32]);
        let missing_storage_path = StoragePath::for_address_and_slot(address, missing_storage_key);
        let result = cursor.seek(missing_storage_path.full_path());
        assert!(result.is_ok());
        // Should find the next storage slot (storage_key2) or the next account
    }
}
