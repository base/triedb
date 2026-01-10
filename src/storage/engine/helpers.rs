//! Helper functions for storage engine operations.
//!
//! This module contains utility functions used across the storage engine
//! for common operations like location calculation, prefix matching, and
//! subtrie manipulation.

use super::Error;
use crate::{
    location::Location,
    node::Node,
    page::{PageId, SlottedPage, SlottedPageMut},
    path::RawPath,
    pointer::Pointer,
};

/// Calculates the appropriate location for a node given its page and index.
///
/// If the node is at index 0 (root of the page), returns a page-based location.
/// Otherwise, returns a cell-based location for same-page references.
pub(super) fn node_location(page_id: PageId, page_index: u8) -> Location {
    if page_index == 0 {
        Location::for_page(page_id)
    } else {
        Location::for_cell(page_index)
    }
}

/// Finds the index of the change with the shortest common prefix shared with the node.
///
/// This function is critical for determining how to navigate the trie during modifications.
/// It returns the index of the change with the shortest common prefix and the length of
/// that common prefix.
///
/// # Parameters
/// - `changes`: Slice of path-value pairs to apply (must be sorted by path)
/// - `path_offset`: Current offset into paths being processed
/// - `node`: The current trie node to compare against
///
/// # Returns
/// A tuple of (change_index, common_prefix_length)
///
/// # Panics
/// Panics if `changes` is empty.
pub(super) fn find_shortest_common_prefix<T>(
    changes: &[(RawPath, T)],
    path_offset: u8,
    node: &Node,
) -> (usize, usize) {
    let leftmost = changes.first().unwrap();
    let leftmost_path = leftmost.0.slice(path_offset as usize..);
    let rightmost = changes.last().unwrap();
    let rightmost_path = rightmost.0.slice(path_offset as usize..);

    debug_assert!(leftmost.0 <= rightmost.0, "changes must be sorted");
    debug_assert!(
        leftmost_path <= rightmost_path,
        "changes must be sorted after slicing with path offset"
    );

    let node_prefix = RawPath::from(node.prefix());
    let leftmost_prefix_length = node_prefix.common_prefix_length(&leftmost_path);
    let rightmost_prefix_length = node_prefix.common_prefix_length(&rightmost_path);

    if leftmost_prefix_length <= rightmost_prefix_length {
        (0, leftmost_prefix_length)
    } else {
        (changes.len() - 1, rightmost_prefix_length)
    }
}

/// Counts the number of nodes in a subtrie rooted at the given index.
///
/// This is used during page splitting to determine which subtrie is largest
/// and should be moved to a new page.
///
/// # Parameters
/// - `page`: The page containing the subtrie
/// - `root_index`: Cell index of the subtrie root
///
/// # Returns
/// The count of nodes in the subtrie (including the root)
pub(super) fn count_subtrie_nodes(page: &SlottedPage<'_>, root_index: u8) -> Result<u8, Error> {
    let mut count = 1; // Count the root node
    let node: Node = page.get_value(root_index)?;
    if !node.has_children() {
        return Ok(count);
    }

    // Count child nodes that are in this page
    for (_, child_ptr) in node.enumerate_children()? {
        if let Some(child_index) = child_ptr.location().cell_index() {
            count += count_subtrie_nodes(page, child_index)?;
        }
    }

    Ok(count)
}

/// Moves an entire subtrie from one page to another.
///
/// This function recursively moves all nodes in a subtrie from the source page
/// to the target page, updating all internal pointers appropriately.
///
/// # Parameters
/// - `source_page`: The page to move nodes from
/// - `root_index`: Cell index of the subtrie root in the source page
/// - `target_page`: The page to move nodes to
///
/// # Returns
/// The new location of the subtrie root in the target page
pub(super) fn move_subtrie_nodes(
    source_page: &mut SlottedPageMut<'_>,
    root_index: u8,
    target_page: &mut SlottedPageMut<'_>,
) -> Result<Location, Error> {
    let node: Node = source_page.get_value(root_index)?;
    source_page.delete_value(root_index)?;

    let has_children = node.has_children();

    // first insert the node into the new page to secure its location.
    let new_index = target_page.insert_value(&node)?;

    // if the node has no children, we're done.
    if !has_children {
        return Ok(node_location(target_page.id(), new_index));
    }

    // otherwise, we need to move the children of the node.
    let mut updated_node: Node = target_page.get_value(new_index)?;

    // Process each child that's in the current page
    let range = if updated_node.is_branch() {
        0..16
    } else {
        // AccountLeaf's only have 1 child
        0..1
    };

    for branch_index in range {
        let child_ptr = if updated_node.is_account_leaf() {
            updated_node.direct_child()?
        } else {
            updated_node.child(branch_index)?
        };
        if let Some(child_ptr) = child_ptr {
            if let Some(child_index) = child_ptr.location().cell_index() {
                // Recursively move its children
                let new_location = move_subtrie_nodes(source_page, child_index, target_page)?;
                // update the pointer in the parent node
                updated_node
                    .set_child(branch_index, Pointer::new(new_location, child_ptr.rlp().clone()))?;
            }
        }
    }

    // update the parent node with the new child pointers.
    target_page.set_value(new_index, &updated_node)?;

    Ok(node_location(target_page.id(), new_index))
}
