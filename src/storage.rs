use std::sync::Arc;
use crate::page::SubtriePage;
use crate::page_manager::PageManager;
use crate::nodes::TrieNode;
use crate::nodes::leaf::LeafNode;
use crate::nodes::branch::BranchNode;
use crate::nodes::reference::NodeReference;
use crate::value::Value;
use alloy_trie::Nibbles;

pub struct StorageManager<P: PageManager> {
    root_node: NodeReference,
    page_manager: P,
}

impl<P: PageManager> StorageManager<P> {
    pub fn new(mut page_manager: P) -> Result<Self, String> {
        // TODO: this is a hack to ensure the page manager has enough space for the root node
        page_manager.resize(100).map_err(|e| format!("Failed to resize page manager: {}", e))?;

        let root_page = page_manager.allocate_page()?;
        let root_node = NodeReference::new_dirty(root_page.0, 0);
        Ok(Self { root_node, page_manager })
    }

    fn root_page<'a>(&self) -> SubtriePage<'a> {
        let page = self.page_manager.get_page(self.root_node.page_id).expect("Page not found");
        let sp = SubtriePage::from_id_and_page(self.root_node.page_id, page);
        println!("Root page!");
        sp.inspect();
        sp
    }

    pub fn get<V: Value>(&mut self, path: Nibbles) -> Option<Arc<V>> {
        let root_node_index = self.root_node.index;

        let page = self.root_page();
        let root_node = &page.get_node(root_node_index).expect("Node not found");
        get_from_node(&self.page_manager, path, root_node, &page)
    }

    pub fn insert<V: Value>(&mut self, path: Nibbles, value: V) -> Result<(), String> {
        // TODO: potentially resize the page manager if there's any risk of running out of space

        let mut subtrie_page = self.root_page();
        let root_node = &self.root_node;
        let root_trie_node = subtrie_page.get_node::<V>(root_node.index);
        self.root_node = if root_trie_node.is_none() {
            let new_node = insert_into_node(&mut self.page_manager, path, value, TrieNode::EmptyRoot, &mut subtrie_page)?;
            subtrie_page.insert(&new_node).expect("Failed to insert node into empty root")
        } else {
            let node = subtrie_page.get_node(root_node.index).unwrap();
            let new_node = insert_into_node(&mut self.page_manager, path, value, node, &mut subtrie_page)?;
            set_or_insert_node(&mut self.page_manager, &mut subtrie_page, &new_node, root_node.index)?
        };
        println!("Inserted!");
        self.root_page().inspect();
        Ok(())
    }

    pub fn delete(&mut self, path: Nibbles) {
        todo!()
    }
    
    pub fn commit<V: Value>(&mut self) -> Result<(), String> {
        let mut root_page = self.root_page();
        if root_page.is_dirty() {
            commit_node::<P, V>(&mut self.page_manager, &self.root_node, &mut root_page)?;
            root_page.set_dirty(false);
            self.page_manager.commit_page(root_page.page_id)?;
        }
        Ok(())
    }

    pub fn print_all<V: Value>(&mut self) -> () {
        let root_page = self.root_page();
        println!("Printing from root page: {:?}", root_page.page_id);
        print_all_recursive::<P, V>(&self.page_manager, &self.root_node, Nibbles::new(), &root_page);
    }
}

fn get_from_node<P: PageManager, V: Value>(page_manager: &P, path: Nibbles, node: &TrieNode<V>, page: &SubtriePage) -> Option<Arc<V>> {
    match node {
        TrieNode::EmptyRoot => None,
        TrieNode::Leaf(leaf) => {
            if leaf.prefix == path {
                Some(leaf.value.clone())
            } else {
                None
            }
        },
        TrieNode::Branch(branch) => {
            let common_prefix_len = path.common_prefix_length(&branch.prefix);
            if common_prefix_len == branch.prefix.len() {
                if common_prefix_len == path.len() {
                    panic!("Path resolves to a branch node, which should not happen");
                } else {
                    let index = path.at(common_prefix_len);
                    let child = branch.get_child(index as u8);
                    if child.is_none() {
                        return None;
                    }

                    let child = child.as_ref().unwrap();
                    let subtrie_page = if child.page_id == page.page_id {
                        page
                    } else {
                        let page = page_manager.get_page(child.page_id).expect("Page not found");
                        &SubtriePage::from_id_and_page(child.page_id, page)
                    };
                    let node = subtrie_page.get_node(child.index).expect("Node not found");

                    get_from_node(page_manager, path.slice(common_prefix_len + 1..), &node, subtrie_page)
                }
            } else {
                None
            }
        },
    }
}

fn print_all_recursive<P: PageManager, V: Value>(page_manager: &P, node: &NodeReference, path: Nibbles, page: &SubtriePage) -> () {        
    let page = if node.page_id == page.page_id {
        page
    } else {
        println!("Using page {}", node.page_id);
        let resolved_page = page_manager.get_page(node.page_id).expect("Page not found");
        &SubtriePage::from_id_and_page(node.page_id, resolved_page)
    };
    let node = page.get_node::<V>(node.index).expect("Node not found");
    print_all_recursive_inner::<P, V>(page_manager, &node, path, page);
}

fn print_all_recursive_inner<P: PageManager, V: Value>(page_manager: &P, node: &TrieNode<V>, path: Nibbles, page: &SubtriePage) -> () {
    match node {
        TrieNode::Leaf(leaf) => {
            println!("{} Leaf: {:?} -> {:?}", " ".repeat(path.len() * 2), path.join(&leaf.prefix), leaf.value);
        }
        TrieNode::Branch(branch) => {
            println!("{} Branch: {:?}", " ".repeat(path.len() * 2), path.join(&branch.prefix));
            for (index, child) in branch.children().enumerate() {
                if child.is_none() {
                    continue;
                }
                println!("{} [{:x?}]:", " ".repeat((path.len() + 1) * 2), index);
                let mut path = path.join(&branch.prefix);
                path.push(index as u8);
                print_all_recursive::<P, V>(page_manager, child.unwrap(), path, page);
            }
        }
        TrieNode::EmptyRoot => {
            println!("Empty root");
        }
    }
}

fn insert_into_node<'a, P: PageManager, V: Value>(
    page_manager: &mut P,
    path: Nibbles,
    value: V,
    node: TrieNode<V>,
    page: &mut SubtriePage<'a>
) -> Result<TrieNode<V>, String> {
    match node {
        TrieNode::EmptyRoot => {
            // replace the empty root with a new leaf
            Ok(LeafNode::new(path, value).into())
        }
        TrieNode::Leaf(leaf) => {
            let common_prefix_len = path.common_prefix_length(&leaf.prefix);

            if common_prefix_len == leaf.prefix.len() {
                if common_prefix_len == path.len() {
                    // full path match, replace the leaf value
                    Ok(leaf.with_value(value).into())
                } else {    
                    // new path is a superset of the leaf path, this is forbidden
                    Err("New value has a longer path than an existing leaf node".to_string())
                }
            } else {
                // insert a new branch at the common prefix, containing the old leaf and a new leaf
                let common_prefix = path.slice(0..common_prefix_len);
                let old_index = leaf.prefix.at(common_prefix_len);
                let old_remainder = leaf.prefix.slice(common_prefix_len + 1..);
                let new_index = path.at(common_prefix_len);
                let new_remainder = path.slice(common_prefix_len + 1..);

                let old_leaf = insert_node(
                    page_manager,
                    &TrieNode::<V>::from(leaf.with_prefix(old_remainder)),
                    page
                )?;
                let new_leaf = insert_node(
                    page_manager,
                    &LeafNode::new(new_remainder, value).into(),
                    page
                )?;

                let mut parent_branch = BranchNode::new(common_prefix);
                parent_branch.set_child(old_index as u8, Some(old_leaf));
                parent_branch.set_child(new_index as u8, Some(new_leaf));

                Ok(parent_branch.into())
            }
        }
        TrieNode::Branch(mut branch) => {
            let common_prefix_len = path.common_prefix_length(&branch.prefix);

            if common_prefix_len == branch.prefix.len() {
                if common_prefix_len == path.len() {
                    panic!("New value would be inserted at an existing branch node");
                } else {
                    // insert into the appropriate child slot of the current branch
                    let child = branch.get_child(path.at(common_prefix_len) as u8);
                    if child.is_none() {
                        // slot is currently empty, insert a new leaf
                        let new_leaf = LeafNode::new(path.slice(common_prefix_len + 1..), value);
                        let node_reference = insert_node(page_manager, &new_leaf.into(), page)?;
                        branch.set_child(path.at(common_prefix_len) as u8, Some(node_reference));
                        return Ok(branch.into());
                    }
                    // slot is currently occupied, recurse into the child
                    let child = child.unwrap();
                    let subtrie_page = if child.page_id == page.page_id {
                        page
                    } else {
                        let page = page_manager.get_page(child.page_id).expect("Page not found");
                        &mut SubtriePage::from_id_and_page(child.page_id, page)
                    };
                    let dereferenced_child = subtrie_page.get_node(child.index).expect("Node not found");
                    let new_node = insert_into_node(page_manager, path.slice(common_prefix_len + 1..), value, dereferenced_child, subtrie_page)?;
                    let node_reference = set_or_insert_node(page_manager, subtrie_page, &new_node, child.index)?;
                    branch.set_child(path.at(common_prefix_len) as u8, Some(node_reference));
                    Ok(branch.into())
                }
            } else {
                // insert a new branch at the common prefix, containing the old branch and a new leaf
                let common_prefix = path.slice(0..common_prefix_len);
                let old_index = branch.prefix.at(common_prefix_len);
                let old_remainder = branch.prefix.slice(common_prefix_len + 1..);
                let new_index = path.at(common_prefix_len);
                let new_remainder = path.slice(common_prefix_len + 1..);

                let old_branch = insert_node(page_manager, &TrieNode::<V>::from(branch.with_prefix(old_remainder)), page)?;
                let new_leaf = insert_node(page_manager, &TrieNode::<V>::from(LeafNode::new(new_remainder, value)), page)?;

                let mut parent_branch = BranchNode::new(common_prefix);
                parent_branch.set_child(old_index as u8, Some(old_branch));
                parent_branch.set_child(new_index as u8, Some(new_leaf));

                Ok(parent_branch.into())
            }
        }
    }
}

fn insert_node<'a, P: PageManager, V: Value>(
    page_manager: &mut P,
    node: &TrieNode<V>,
    page: &mut SubtriePage<'a>
) -> Result<NodeReference, String> {
    if let Some(node_ref) = page.insert(node) {
        return Ok(node_ref);
    }
    // WARNING: this allocation may destroy all existing page references if the file size grows!!!
    // TODO: properly split the page instead of just allocating a new one
    let new_page = page_manager.allocate_page()?;
    let mut new_subtrie_page = SubtriePage::from_identified_page(new_page);
    let node_ref = new_subtrie_page.insert(node).expect("Failed to insert node into newly-allocated page");
    *page = new_subtrie_page;
    Ok(node_ref)
}

fn set_or_insert_node<'a, P: PageManager, V: Value>(
    page_manager: &mut P,
    page: &mut SubtriePage<'a>,
    node: &TrieNode<V>,
    index: u8
) -> Result<NodeReference, String> {
    if let Some(node_ref) = page.set_node(index, node) {
        return Ok(node_ref);
    }
    page.pop_node::<V>(index).ok_or("Failed to remove node from page")?;
    insert_node(page_manager, node, page)
}

fn commit_node<'a, P: PageManager, V: Value>(
    page_manager: &mut P,
    node: &NodeReference,
    page: &SubtriePage
) -> Result<(), String> {
    if !page.is_dirty() {
        return Ok(());
    }

   if node.page_id == page.page_id {
        if let Some(TrieNode::Branch(branch)) = page.get_node::<V>(node.index) {
            let children: Vec<_> = branch.children().filter_map(|child| child).collect();
            for child_ref in children {
                commit_node::<P, V>(page_manager, &child_ref, page)?;
            }
        }
        Ok(())
    } else {
        let external_page = page_manager.get_page(node.page_id).expect("Page not found");
        let subtrie_page = SubtriePage::from_id_and_page(node.page_id, external_page);
        if let Some(TrieNode::Branch(branch)) = subtrie_page.get_node::<V>(node.index) {
            let children: Vec<_> = branch.children().filter_map(|child| child).collect();
            for child_ref in children {
                commit_node::<P, V>(page_manager, &child_ref, &subtrie_page)?;
            }
        }
        // page.set_dirty(false);
        page_manager.commit_page(subtrie_page.page_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::page_manager::MemoryMappedFilePageManager;

    #[test]
    fn test_insert_and_get() -> Result<(), String> {
        let page_manager = MemoryMappedFilePageManager::new("test.db").unwrap();
        let mut storage = StorageManager::new(page_manager)?;
        storage.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), "value1".to_string())?;
        storage.print_all::<String>();
        assert_eq!(storage.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x03])), Some(Arc::new("value1".to_string())));

        storage.insert(Nibbles::from_nibbles(&[0x04, 0x05, 0x06]), "value2".to_string())?;
        storage.print_all::<String>();
        assert_eq!(storage.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x03])), Some(Arc::new("value1".to_string())));
        assert_eq!(storage.get(Nibbles::from_nibbles(&[0x04, 0x05, 0x06])), Some(Arc::new("value2".to_string())));

        storage.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x0f]), "value3".to_string())?;
        storage.print_all::<String>();
        assert_eq!(storage.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x03])), Some(Arc::new("value1".to_string())));
        assert_eq!(storage.get(Nibbles::from_nibbles(&[0x04, 0x05, 0x06])), Some(Arc::new("value2".to_string())));
        assert_eq!(storage.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x0f])), Some(Arc::new("value3".to_string())));

        Ok(())
    }

    #[test]
    fn test_insert_commit_get() -> Result<(), String> {
        let page_manager = MemoryMappedFilePageManager::new("test.db").unwrap();
        let mut storage = StorageManager::new(page_manager)?;
        storage.insert(Nibbles::from_nibbles(&[0x01, 0x02, 0x03]), "value1".to_string())?;
        storage.print_all::<String>();
        assert_eq!(storage.root_page().is_dirty(), true);
        storage.commit::<String>()?;

        assert_eq!(storage.root_page().is_dirty(), false);
        assert_eq!(storage.get(Nibbles::from_nibbles(&[0x01, 0x02, 0x03])), Some(Arc::new("value1".to_string())));
        storage.print_all::<String>();

        Ok(())
    }
}
