use crate::{
    context::TransactionContext,
    meta::{MetadataManager, OpenMetadataError},
    node::{
        Node,
        NodeKind::{AccountLeaf, Branch, StorageLeaf},
        TrieValue,
    },
    page::{Page, PageId, PageManager, SlottedPage},
    path::RawPath,
    pointer::Pointer,
    snapshot::SnapshotId,
    storage::{
        engine::{Error, StorageEngine},
        value::Value,
    },
};
use std::{collections::HashSet, fmt::Debug, io, path::Path};

#[derive(Default)]
pub struct DebugPage {
    pub nodes_per_page: DebugStats,
    pub bytes_per_page: DebugStats,
    pub depth_of_trie_in_nodes: DebugStats,
    pub depth_of_trie_in_pages: DebugStats,
    pub path_prefix_length: DebugStats,
    pub num_children_per_branch: DebugStats,
    pub node_size_in_bytes: DebugStats,
}

impl Debug for DebugPage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\nNodes Per Page: {:?}\nBytes Per Page: {:?}\nDepth of Trie in Nodes: {:?}\nDepth of Trie in Pages: {:?}\nPath Prefix Length: {:?}\nNum Children Per Branch: {:?}\nNode Size in Bytes: {:?}", self.nodes_per_page, self.bytes_per_page, self.depth_of_trie_in_nodes, self.depth_of_trie_in_pages, self.path_prefix_length, self.num_children_per_branch, self.node_size_in_bytes)
    }
}

pub struct DebugStats {
    min: usize,
    max: usize,
    total_sum: usize,
    count: usize,
}

impl DebugStats {
    pub fn update_stats(&mut self, new_val: usize) {
        if new_val > self.max {
            self.max = new_val;
        }
        if new_val < self.min {
            self.min = new_val;
        }
        self.total_sum += new_val;
        self.count += 1;
    }
}

impl Default for DebugStats {
    fn default() -> Self {
        Self { min: usize::MAX, max: usize::MIN, total_sum: 0, count: 0 }
    }
}

impl Debug for DebugStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "min: {}, max: {}, total sum: {}, count: {}, mean: {}",
            self.min,
            self.max,
            self.total_sum,
            self.count,
            self.total_sum as f64 / self.count as f64
        )
    }
}

/// StorageDebugger provides debugging utilities for examining the internal structure
/// of the storage engine, including page contents, trie statistics, and consistency checks.
#[derive(Debug)]
pub struct StorageDebugger<'a> {
    page_manager: &'a PageManager,
}

impl<'a> StorageDebugger<'a> {
    /// Creates a new StorageDebugger with references to the storage engine components.
    pub fn new(page_manager: &'a PageManager) -> Self {
        Self { page_manager }
    }

    /// Prints the structure of a page or the entire database starting from the root.
    pub fn print_page<W: io::Write>(
        &self,
        context: &TransactionContext,
        mut buf: W,
        page_id: Option<PageId>,
    ) -> Result<(), Error> {
        let root_node_page_id = match context.root_node_page_id {
            None => return Ok(()),
            Some(page_id) => page_id,
        };

        let (page, print_whole_db) = match page_id {
            Some(id) => (self.get_page(context, id)?, false),
            None => (self.get_page(context, root_node_page_id)?, true),
        };

        let slotted_page = SlottedPage::try_from(page)?;
        self.print_page_helper(
            context,
            slotted_page,
            0,
            String::from(""),
            buf.by_ref(),
            print_whole_db,
        )
    }

    /// Recursive helper for printing page structure.
    fn print_page_helper(
        &self,
        context: &TransactionContext,
        slotted_page: SlottedPage<'_>,
        cell_index: u8,
        indent: String,
        buf: &mut impl io::Write,
        print_whole_db: bool,
    ) -> Result<(), Error> {
        let node: Node = slotted_page.get_value(cell_index)?;

        match node.kind() {
            AccountLeaf { ref storage_root, .. } => {
                Self::write_node_value(&node, slotted_page.id(), buf, &indent)?;
                let mut new_indent = indent.clone();
                new_indent.push('\t');

                if let Some(direct_child) = storage_root {
                    let (new_slotted_page, cell_index) =
                        self.get_slotted_page_and_index(context, direct_child, slotted_page)?;
                    // child is on different page, and we are only printing the current page
                    if new_slotted_page.id() != slotted_page.id() && !print_whole_db {
                        let child_page_id = direct_child.location().page_id().unwrap();
                        writeln!(buf, "{new_indent}Child on new page: {child_page_id:?}")?;
                        Ok(())
                    } else {
                        self.print_page_helper(
                            context,
                            new_slotted_page,
                            cell_index,
                            new_indent,
                            buf,
                            print_whole_db,
                        )
                    }
                } else {
                    writeln!(buf, "{new_indent}No direct child")?;
                    Ok(())
                }
            }

            Branch { ref children } => {
                Self::write_node_value(&node.clone(), slotted_page.id(), buf, &indent)?;
                for child in children.iter().flatten() {
                    let mut new_indent = indent.clone();
                    new_indent.push('\t');

                    //check if child is on same page
                    let (new_slotted_page, cell_index) =
                        self.get_slotted_page_and_index(context, child, slotted_page)?;
                    // child is on new page, and we are only printing the current page
                    if new_slotted_page.id() != slotted_page.id() && !print_whole_db {
                        let child_page_id = child.location().page_id().unwrap();
                        writeln!(buf, "{new_indent}Child on new page: {child_page_id:?}")?;
                        return Ok(());
                    } else {
                        self.print_page_helper(
                            context,
                            new_slotted_page,
                            cell_index,
                            new_indent,
                            buf,
                            print_whole_db,
                        )?
                    }
                }
                Ok(())
            }
            StorageLeaf { .. } => {
                Self::write_node_value(&node, slotted_page.id(), buf, &indent)?;
                Ok(())
            }
        }
    }

    /// Prints information about a given TrieValue.
    /// Verbose option: writes information about nodes visited along the path to file
    /// Extra-verbose option: writes information about pages visited along path to file
    pub fn print_path<W: io::Write>(
        &self,
        context: &TransactionContext,
        path: &RawPath,
        mut buf: W,
        verbosity_level: u8,
    ) -> Result<(), Error> {
        let page_id = match context.root_node_page_id {
            None => return Ok(()),
            Some(page_id) => page_id,
        };
        let page = self.get_page(context, page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;

        // If extra_verbose, print the root page first
        match verbosity_level {
            0 => (),
            1 => {
                //verbose; print page ID and nodes accessed from page
                writeln!(buf, "\nNODES ACCESSED FROM PAGE {page_id}\n")?;
            }
            2 => {
                //extra verbose; print page ID, nodes accessed from page, and page contents
                writeln!(buf, "PAGE: {page_id}\n")?;

                self.print_page(context, &mut buf, Some(page_id))?;
                writeln!(buf, "\nNODES ACCESSED FROM PAGE {page_id}:")?;
            }
            _ => return Err(Error::DebugError("Invalid verbosity level".to_string())),
        }

        self.print_path_helper(context, path, 0, slotted_page, 0, buf.by_ref(), verbosity_level)
    }

    /// Recursive helper for printing path traversal.
    fn print_path_helper(
        &self,
        context: &TransactionContext,
        path: &RawPath,
        path_offset: usize,
        slotted_page: SlottedPage<'_>,
        page_index: u8,
        buf: &mut impl io::Write,
        verbosity_level: u8,
    ) -> Result<(), Error> {
        let node: Node = slotted_page.get_value(page_index)?;

        if verbosity_level > 0 {
            // Write node information with indentation
            Self::write_node_value(&node, slotted_page.id(), buf, "")?;
        }

        let common_prefix_length =
            path.slice(path_offset..).common_prefix_length(&node.prefix().into());

        if common_prefix_length < node.prefix().len() {
            writeln!(buf, "NODE NOT FOUND\n")?;
            return Ok(());
        }

        let remaining_path = path.slice(path_offset + common_prefix_length..);

        if remaining_path.is_empty() {
            //write only this node's information to file
            writeln!(buf, "\n\nREQUESTED NODE:")?;
            Self::write_node_value(&node, slotted_page.id(), buf, "")?;

            return Ok(());
        }

        let (child_pointer, new_path_offset) = match node.kind() {
            AccountLeaf { ref storage_root, .. } => {
                (storage_root.as_ref(), path_offset + common_prefix_length)
            }
            Branch { ref children } => (
                children[remaining_path.get_unchecked(0) as usize].as_ref(),
                path_offset + common_prefix_length + 1,
            ),
            _ => unreachable!(),
        };

        match child_pointer {
            Some(child_pointer) => {
                let (child_slotted_page, child_cell_index) =
                    self.get_slotted_page_and_index(context, child_pointer, slotted_page)?;

                // If we're moving to a new page and extra_verbose is true, print the new page
                if child_slotted_page.id() != slotted_page.id() {
                    if verbosity_level == 2 {
                        //extra verbose; print new page contents
                        writeln!(buf, "\n\n\nNEW PAGE: {}\n", child_slotted_page.id())?;
                        self.print_page(context, &mut *buf, Some(child_slotted_page.id()))?;
                    }

                    if verbosity_level > 0 {
                        writeln!(buf, "\nNODES ACCESSED FROM PAGE {}\n", child_slotted_page.id())?;
                    }
                }

                self.print_path_helper(
                    context,
                    path,
                    new_path_offset,
                    child_slotted_page,
                    child_cell_index,
                    buf,
                    verbosity_level,
                )
            }

            None => {
                writeln!(buf, "NODE NOT FOUND\n")?;
                Ok(())
            }
        }
    }

    /// Helper function to convert node information to string for printing/writing to file.
    fn write_node_value<W: io::Write>(
        node: &Node,
        page_id: PageId,
        buf: &mut W,
        indent: &str,
    ) -> Result<(), Error> {
        let prefix = node.prefix();
        match node.kind() {
            Branch { ref children } => {
                writeln!(
                    buf,
                    "{}Branch Node:  Page ID: {}  Children: [{}], Prefix: {}",
                    indent,
                    page_id,
                    children.iter().enumerate().filter(|(_, child)| child.is_some()).fold(
                        String::new(),
                        |mut s, (i, _)| {
                            if !s.is_empty() {
                                s.push_str(", ")
                            };
                            s.push_str(&i.to_string());
                            s
                        }
                    ),
                    alloy_primitives::hex::encode(prefix.pack())
                )?;
                Ok(())
            }
            AccountLeaf { .. } => {
                match node.value() {
                    Ok(TrieValue::Account(acct)) => {
                        writeln!(
                            buf,
                            "{}AccountLeaf: nonce: {:?}, balance: {:?}, prefix: {}, code_hash: {:x?}, storage_root: {:?}",
                            indent,
                            acct.nonce, acct.balance, alloy_primitives::hex::encode(prefix.pack()), acct.code_hash, acct.storage_root,
                        )?;
                    }
                    _ => {
                        writeln!(buf, "{indent}AccountLeaf: no value ")?;
                    }
                };
                Ok(())
            }
            StorageLeaf { .. } => {
                match node.value() {
                    Ok(TrieValue::Storage(strg)) => {
                        let str_prefix = alloy_primitives::hex::encode(prefix.pack());
                        writeln!(
                            buf,
                            "{indent}StorageLeaf: storage: {strg:?}, prefix: {str_prefix}"
                        )?;
                    }
                    _ => {
                        writeln!(buf, "{indent}StorageLeaf: no value")?;
                    }
                };
                Ok(())
            }
        }
    }

    /// Computes and prints various statistics about the trie structure.
    pub fn debug_statistics<W: io::Write>(
        &self,
        context: &TransactionContext,
        mut buf: W,
    ) -> Result<(), Error> {
        let page_id = match context.root_node_page_id {
            None => return Ok(()),
            Some(page_id) => page_id,
        };
        let page = self.get_page(context, page_id)?;
        let slotted_page = SlottedPage::try_from(page)?;

        let mut stats = DebugPage::default();

        let occupied_bytes = slotted_page.num_occupied_bytes();
        let occupied_cells = slotted_page.num_occupied_cells();

        stats.bytes_per_page.update_stats(occupied_bytes);
        stats.nodes_per_page.update_stats(occupied_cells);

        self.debug_statistics_helper(context, slotted_page, 0, 1, 1, &mut stats)?;

        writeln!(buf, "Page Statistics: {stats:?}")?;
        Ok(())
    }

    /// Recursive helper for computing trie statistics.
    fn debug_statistics_helper(
        &self,
        context: &TransactionContext,
        slotted_page: SlottedPage<'_>,
        cell_index: u8,
        node_depth: usize,
        page_depth: usize,
        stats: &mut DebugPage,
    ) -> Result<(), Error> {
        let node: Node = slotted_page.get_value(cell_index)?;

        //update stats: total node size and prefix length
        stats.node_size_in_bytes.update_stats(node.size());
        stats.path_prefix_length.update_stats(node.prefix().len());

        match node.kind() {
            AccountLeaf { ref storage_root, .. } => {
                //Note: direct child is not counted as part of stats.num_children
                if let Some(direct_child) = storage_root {
                    let (new_slotted_page, cell_index) =
                        self.get_slotted_page_and_index(context, direct_child, slotted_page)?;
                    //if we move to a new page, update relevent stats
                    if new_slotted_page.id() != slotted_page.id() {
                        let occupied_bytes = new_slotted_page.num_occupied_bytes();
                        let occupied_cells = new_slotted_page.num_occupied_cells();

                        stats.bytes_per_page.update_stats(occupied_bytes);
                        stats.nodes_per_page.update_stats(occupied_cells);

                        self.debug_statistics_helper(
                            context,
                            new_slotted_page,
                            cell_index,
                            node_depth + 1,
                            page_depth + 1,
                            stats,
                        )
                    } else {
                        self.debug_statistics_helper(
                            context,
                            new_slotted_page,
                            cell_index,
                            node_depth + 1,
                            page_depth,
                            stats,
                        )
                    }
                } else {
                    stats.depth_of_trie_in_nodes.update_stats(node_depth);
                    stats.depth_of_trie_in_pages.update_stats(page_depth);
                    Ok(())
                }
            }

            Branch { ref children } => {
                //update num children per branch
                let child_iter = children.iter().flatten();
                let num_children = child_iter.clone().count();
                stats.num_children_per_branch.update_stats(num_children);

                for child in child_iter {
                    //check if child is on same page
                    let (new_slotted_page, cell_index) =
                        self.get_slotted_page_and_index(context, child, slotted_page)?;
                    //update page depth if we move to a new page
                    if new_slotted_page.id() != slotted_page.id() {
                        let occupied_bytes = new_slotted_page.num_occupied_bytes();
                        let occupied_cells = new_slotted_page.num_occupied_cells();

                        stats.bytes_per_page.update_stats(occupied_bytes);
                        stats.nodes_per_page.update_stats(occupied_cells);
                        self.debug_statistics_helper(
                            context,
                            new_slotted_page,
                            cell_index,
                            node_depth + 1,
                            page_depth + 1,
                            stats,
                        )?
                    } else {
                        self.debug_statistics_helper(
                            context,
                            new_slotted_page,
                            cell_index,
                            node_depth + 1,
                            page_depth,
                            stats,
                        )?
                    }
                }
                Ok(())
            }
            StorageLeaf { .. } => {
                stats.depth_of_trie_in_pages.update_stats(page_depth);
                stats.depth_of_trie_in_nodes.update_stats(node_depth);
                Ok(())
            }
        }
    }

    /// This check verifies:
    /// 1. All pages are correctly classified as reachable, orphaned, or unreachable
    /// 2. No pages are both reachable and orphaned (data integrity violation)
    /// 3. No pages are unreachable (memory leak)
    /// 4. Snapshot ID consistency: each child page's snapshot ID must be <= parent's snapshot ID
    /// 5. No cycles exist in the trie structure (prevents infinite recursion)
    pub fn database_consistency_check<W: io::Write>(
        &self,
        mut buf: W,
        file_path: impl AsRef<Path>,
        storage_engine: &StorageEngine,
    ) -> Result<(), Error> {
        let db_file_path = file_path.as_ref();

        let mut meta_file_path = db_file_path.to_path_buf();
        meta_file_path.as_mut_os_string().push(".meta");
        let mut meta_manager = match MetadataManager::open(&meta_file_path) {
            Ok(manager) => manager,
            Err(OpenMetadataError::Corrupted) => {
                writeln!(buf, "Metadata file corruption detected: {meta_file_path:?}")
                    .map_err(Error::IO)?;

                // Provide additional debugging information
                if let Ok(file_meta) = std::fs::metadata(&meta_file_path) {
                    writeln!(buf, "File size: {} bytes", file_meta.len()).map_err(Error::IO)?;
                    if let Ok(modified) = file_meta.modified() {
                        writeln!(buf, "Last modified: {modified:?}").map_err(Error::IO)?;
                    }
                }
                return Err(Error::IO(io::Error::other("Metadata file corrupted")));
            }
            Err(e) => {
                return Err(Error::IO(io::Error::other(format!("Failed to open metadata: {e:?}"))))
            }
        };

        let context = storage_engine.read_context();
        let active_slot_page_id = meta_manager.active_slot().root_node_page_id();

        // Get all pages reachable from the committed state
        let mut reachable_pages = self.consistency_check(active_slot_page_id, &context)?;

        // Also account for dirty pages that haven't been committed yet
        let dirty_pages = self.get_dirty_pages()?;
        reachable_pages.extend(&dirty_pages);

        let orphaned_pages = meta_manager
            .orphan_pages()
            .iter()
            .map(|orphan| orphan.page_id())
            .collect::<HashSet<_>>();

        let reachable_orphaned_pages: HashSet<PageId> =
            orphaned_pages.intersection(&reachable_pages).cloned().collect();

        let page_count = storage_engine.size();

        let all_pages: HashSet<PageId> = (1..page_count)
            .map(|id| PageId::new(id).unwrap()) // Unwrap Option from new()
            .collect();

        let mut reachable_or_orphaned: HashSet<PageId> = reachable_pages.into_iter().collect();
        reachable_or_orphaned.extend(&orphaned_pages);

        // Unreachable pages = all_pages - reachable_or_orphaned
        let unreachable_pages: HashSet<PageId> =
            all_pages.difference(&reachable_or_orphaned).cloned().collect();

        // Check for errors and flag them
        let mut has_errors = false;

        if !reachable_orphaned_pages.is_empty() {
            writeln!(buf, "ERROR: Reachable Orphaned Pages: {reachable_orphaned_pages:?}")
                .map_err(Error::IO)?;
            has_errors = true;
        }

        if !unreachable_pages.is_empty() {
            writeln!(buf, "ERROR: Unreachable Pages: {unreachable_pages:?}").map_err(Error::IO)?;
            has_errors = true;
        }

        if has_errors {
            return Err(Error::IO(io::Error::new(
                io::ErrorKind::InvalidData,
                "Database consistency check failed: inconsistencies detected",
            )));
        }

        writeln!(buf, "Consistency check passed: database is consistent").map_err(Error::IO)?;
        Ok(())
    }

    /// Traverses the trie from the given root node page id and returns a list of all reachable
    /// PageIds.
    ///
    /// This method performs several consistency checks:
    /// - Validates that child pages have snapshot IDs <= parent snapshot IDs
    /// - Detects cycles in the trie structure to prevent infinite recursion
    /// - Returns all reachable page IDs for further analysis
    pub fn consistency_check(
        &self,
        root_node_page_id: Option<PageId>,
        context: &TransactionContext,
    ) -> Result<HashSet<PageId>, Error> {
        let mut reachable = HashSet::new();
        let mut visited_nodes = HashSet::new();

        // Start from the provided root node page id (if any)
        if let Some(root_page_id) = root_node_page_id {
            reachable.insert(root_page_id);
            let root_page = self.get_page(context, root_page_id)?;
            let root_snapshot_id = root_page.snapshot_id();
            self.consistency_check_helper(
                context,
                root_page_id,
                0,
                root_snapshot_id,
                &mut reachable,
                &mut visited_nodes,
            )?;
        }

        Ok(reachable)
    }

    /// Recursive helper for consistency checking.
    fn consistency_check_helper(
        &self,
        context: &TransactionContext,
        page_id: PageId,
        cell_index: u8,
        parent_snapshot_id: SnapshotId,
        reachable: &mut HashSet<PageId>,
        visited_nodes: &mut HashSet<(PageId, u8)>,
    ) -> Result<(), Error> {
        let node_key = (page_id, cell_index);

        // Check for cycles to prevent infinite recursion
        if visited_nodes.contains(&node_key) {
            return Err(Error::DebugError(format!(
                "Cycle detected in trie: node (page_id={}, cell_index={}) has already been visited",
                page_id.as_u32(),
                cell_index
            )));
        }

        // Mark this node as visited
        visited_nodes.insert(node_key);

        let page = self.get_page(context, page_id)?;
        let current_snapshot_id = page.snapshot_id();

        // Check snapshot ID consistency: child snapshot should be <= parent snapshot
        if current_snapshot_id > parent_snapshot_id {
            visited_nodes.remove(&node_key); // Clean up before returning error
            return Err(Error::DebugError(format!(
                "Snapshot ID consistency violation: page {} has snapshot ID {} which is greater than parent snapshot ID {}",
                page_id.as_u32(),
                current_snapshot_id,
                parent_snapshot_id
            )));
        }

        let slotted_page = SlottedPage::try_from(page)?;
        let node: Node = slotted_page.get_value(cell_index)?;

        let result = match node.kind() {
            AccountLeaf { ref storage_root, .. } => {
                if let Some(direct_child) = storage_root {
                    let (new_slotted_page, new_cell_index) =
                        self.get_slotted_page_and_index(context, direct_child, slotted_page)?;
                    // If child is on a new page, insert the page into the set and recurse
                    if new_slotted_page.id() != page_id {
                        reachable.insert(new_slotted_page.id());
                        self.consistency_check_helper(
                            context,
                            new_slotted_page.id(),
                            new_cell_index,
                            current_snapshot_id,
                            reachable,
                            visited_nodes,
                        )
                    } else {
                        self.consistency_check_helper(
                            context,
                            page_id,
                            new_cell_index,
                            current_snapshot_id,
                            reachable,
                            visited_nodes,
                        )
                    }
                } else {
                    Ok(())
                }
            }
            Branch { ref children } => {
                for child in children.iter().flatten() {
                    let (new_slotted_page, new_cell_index) =
                        self.get_slotted_page_and_index(context, child, slotted_page)?;
                    if new_slotted_page.id() != page_id {
                        reachable.insert(new_slotted_page.id());
                        self.consistency_check_helper(
                            context,
                            new_slotted_page.id(),
                            new_cell_index,
                            current_snapshot_id,
                            reachable,
                            visited_nodes,
                        )?;
                    } else {
                        self.consistency_check_helper(
                            context,
                            page_id,
                            new_cell_index,
                            current_snapshot_id,
                            reachable,
                            visited_nodes,
                        )?;
                    }
                }
                Ok(())
            }
            StorageLeaf { .. } => Ok(()),
        };

        // Remove this node from visited set before returning (backtrack)
        visited_nodes.remove(&node_key);
        result
    }

    /// Returns all pages that are currently in the Dirty state.
    ///
    /// This method scans all allocated pages and returns those that are
    /// currently being written to (in Dirty state).
    pub fn get_dirty_pages(&self) -> Result<HashSet<PageId>, Error> {
        let mut dirty_pages = HashSet::new();
        let page_count = self.page_manager.size();

        for page_id_raw in 1..=page_count {
            if let Some(page_id) = PageId::new(page_id_raw) {
                if self.page_manager.is_dirty(page_id).map_err(Error::PageError)? {
                    dirty_pages.insert(page_id);
                }
            }
        }

        Ok(dirty_pages)
    }

    /// Helper function to get a slotted page and index from a pointer.
    fn get_slotted_page_and_index<'b>(
        &'b self,
        context: &TransactionContext,
        pointer: &Pointer,
        current_slotted_page: SlottedPage<'b>,
    ) -> Result<(SlottedPage<'b>, u8), Error> {
        let location = pointer.location();
        if let Some(cell_index) = location.cell_index() {
            Ok((current_slotted_page, cell_index))
        } else {
            let page_id = location.page_id().unwrap();
            let page = self.get_page(context, page_id)?;
            let slotted_page = SlottedPage::try_from(page)?;
            Ok((slotted_page, 0))
        }
    }

    /// Helper function to get a page from the page manager.
    fn get_page(&self, context: &TransactionContext, page_id: PageId) -> Result<Page<'_>, Error> {
        self.page_manager.get(context.snapshot_id, page_id).map_err(Error::PageError)
    }

    /// Prints information about the root page and database metadata.
    ///
    /// This includes:
    /// - Root Node Page ID
    /// - Total Page Count
    /// - List of Orphaned Pages
    pub fn root_page_info<W: io::Write>(
        &self,
        mut buf: W,
        file_path: impl AsRef<Path>,
    ) -> Result<(), Error> {
        let db_file_path = file_path.as_ref();

        let mut meta_file_path = db_file_path.to_path_buf();
        meta_file_path.as_mut_os_string().push(".meta");
        let mut meta_manager = MetadataManager::open(meta_file_path)
            .map_err(|e| Error::IO(io::Error::other(format!("Failed to open metadata: {e:?}"))))?;

        let page_count = meta_manager.active_slot().page_count();
        let active_slot = meta_manager.active_slot();
        let root_node_page_id = active_slot.root_node_page_id();
        let orphaned_page_list = meta_manager.orphan_pages().iter().collect::<Vec<_>>();

        writeln!(buf, "Root Node Page ID: {root_node_page_id:?}").map_err(Error::IO)?;
        writeln!(buf, "Total Page Count: {page_count:?}").map_err(Error::IO)?;
        writeln!(buf, "Orphaned Pages: {orphaned_page_list:?}").map_err(Error::IO)?;

        Ok(())
    }
}
