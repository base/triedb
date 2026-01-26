//! Page operations for the storage engine.
//!
//! This module contains functions for page-level operations including:
//! - Allocating new pages
//! - Orphaning (marking for reuse) pages
//! - Cloning pages for copy-on-write
//! - Splitting pages when they become full
//! - Deleting and orphaning subtries

use super::{helpers, Error, StorageEngine};
use crate::{
    context::TransactionContext,
    location::Location,
    meta::OrphanPage,
    node::Node,
    page::{Page, PageId, PageMut, SlottedPage, SlottedPageMut},
    pointer::Pointer,
};
use std::sync::atomic::Ordering;

impl StorageEngine {
    /// Allocates a new page from the underlying page manager.
    ///
    /// If there is an orphaned page available as of the given [SnapshotId],
    /// it is reused instead of allocating fresh storage.
    pub fn allocate_page(&self, context: &mut TransactionContext) -> Result<PageMut<'_>, Error> {
        let alive_snapshot = self.alive_snapshot.load(Ordering::Relaxed);
        let orphaned_page_id = self
            .meta_manager
            .lock()
            .orphan_pages()
            .pop(alive_snapshot)
            .map(|orphan| orphan.page_id());

        let page_to_return = if let Some(orphaned_page_id) = orphaned_page_id {
            let mut page = self.get_mut_page(context, orphaned_page_id)?;
            page.set_snapshot_id(context.snapshot_id);
            page.contents_mut().fill(0);
            context.transaction_metrics.inc_pages_reallocated();
            page
        } else {
            let page = self.page_manager.allocate(context.snapshot_id)?;
            context.transaction_metrics.inc_pages_allocated();
            page
        };

        context.page_count = self.page_manager.size();

        Ok(page_to_return)
    }

    /// Commits all outstanding data to disk.
    pub fn commit(&self, context: &TransactionContext) -> Result<(), Error> {
        self.page_manager.sync()?;

        let mut meta_manager = self.meta_manager.lock();
        let dirty_meta = meta_manager.dirty_slot_mut();
        context.update_metadata(dirty_meta);
        meta_manager.commit()?;

        Ok(())
    }

    /// Retrieves a mutable [Page] from the underlying [PageManager].
    pub fn get_mut_page(
        &self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<PageMut<'_>, Error> {
        let page = self.page_manager.get_mut(context.snapshot_id, page_id)?;
        context.transaction_metrics.inc_pages_read();
        Ok(page)
    }

    /// Retrieves a read-only [Page] from the underlying [PageManager].
    pub fn get_page(
        &self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<Page<'_>, Error> {
        let page = self.page_manager.get(context.snapshot_id, page_id)?;
        context.transaction_metrics.inc_pages_read();
        Ok(page)
    }

    /// Mark a given page as no longer in use (orphan).
    ///
    /// Orphaned pages can be reused for new allocations once the snapshot
    /// that orphaned them is no longer active.
    pub(super) fn orphan_page(
        &self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<(), Error> {
        let orphan = OrphanPage::new(page_id, context.snapshot_id);
        self.meta_manager.lock().orphan_pages().push(orphan).map_err(Error::from)
    }

    /// Retrieves a mutable clone of a [Page] from the underlying [PageManager].
    ///
    /// This implements copy-on-write semantics: if the page belongs to the current
    /// snapshot, it's returned directly. Otherwise, the original page is copied to
    /// a new page, the original is orphaned, and the new page is returned.
    pub(super) fn get_mut_clone(
        &self,
        context: &mut TransactionContext,
        page_id: PageId,
    ) -> Result<PageMut<'_>, Error> {
        let original_page = self.page_manager.get(context.snapshot_id, page_id)?;
        context.transaction_metrics.inc_pages_read();

        // if the page already has the correct snapshot id, return it without cloning.
        if original_page.snapshot_id() == context.snapshot_id {
            return self
                .page_manager
                .get_mut(context.snapshot_id, page_id)
                .map_err(Error::PageError);
        }

        let mut new_page = self.allocate_page(context)?;
        new_page.contents_mut().copy_from_slice(original_page.contents());

        self.orphan_page(context, page_id)?;

        Ok(new_page)
    }

    /// Retrieves a read-only [SlottedPage] from the underlying [PageManager].
    pub(crate) fn get_slotted_page(
        &self,
        context: &TransactionContext,
        page_id: PageId,
    ) -> Result<SlottedPage<'_>, Error> {
        let page = self.get_page(context, page_id)?;
        Ok(SlottedPage::try_from(page)?)
    }

    /// Splits the page into two, moving the largest immediate subtrie of the root node
    /// to a new child page.
    ///
    /// This is called when a page doesn't have enough space for new nodes. The algorithm:
    /// 1. Find all children of the root node that are on this page
    /// 2. Sort them by subtrie size (descending)
    /// 3. Move the largest subtries to new pages until enough space is freed
    pub(super) fn split_page(
        &self,
        context: &mut TransactionContext,
        page: &mut SlottedPageMut<'_>,
    ) -> Result<(), Error> {
        // count subtrie node and sort in desc order
        let root_node: Node = page.get_value(0)?;
        let children = root_node.enumerate_children()?;
        let mut children_with_count = children
            .into_iter()
            .filter(|(_, ptr)| ptr.location().cell_index().is_some())
            .map(|(i, ptr)| {
                let cell_index = ptr.location().cell_index().unwrap();
                (i, ptr, helpers::count_subtrie_nodes(page, cell_index).unwrap_or(0))
            })
            .collect::<Vec<_>>();
        children_with_count.sort_by(|a, b| b.2.cmp(&a.2));

        let mut rest: &[(u8, &Pointer, u8)] = &children_with_count;
        let mut root_node: Node = page.get_value(0)?;

        while page.num_free_bytes() < Page::DATA_SIZE / 4_usize {
            let child_page = self.allocate_page(context)?;
            let mut child_slotted_page = SlottedPageMut::try_from(child_page)?;

            // Find the child with the largest subtrie
            let largest_child: &(u8, &Pointer, u8);
            (largest_child, rest) = rest.split_first().unwrap();
            let (largest_child_index, largest_child_pointer, _) = *largest_child;

            let location = helpers::move_subtrie_nodes(
                page,
                largest_child_pointer.location().cell_index().unwrap(),
                &mut child_slotted_page,
            )?;
            debug_assert!(
                location.page_id().is_some(),
                "expected subtrie to be moved to a new page"
            );

            // Update the pointer in the root node to point to the new page
            root_node.set_child(
                largest_child_index,
                Pointer::new(
                    Location::for_page(child_slotted_page.id()),
                    largest_child_pointer.rlp().clone(),
                ),
            )?;
        }
        page.set_value(0, &root_node)?;

        Ok(())
    }

    /// Recursively deletes a subtrie from the page, orphaning any pages that become
    /// fully unreferenced as a result.
    ///
    /// This is used when deleting an account with storage - all storage nodes must
    /// also be deleted.
    pub(super) fn delete_subtrie(
        &self,
        context: &mut TransactionContext,
        slotted_page: &mut SlottedPageMut<'_>,
        cell_index: u8,
    ) -> Result<(), Error> {
        if cell_index == 0 {
            // if we are a root node, deleting ourself will orphan our entire page and
            // all of our descendant pages. Instead of deleting each cell one-by-one
            // we can orphan our entire page, and recursively orphan all our descendant
            // pages as well.
            return self.orphan_subtrie(context, slotted_page, cell_index);
        }

        let node: Node = slotted_page.get_value(cell_index)?;

        if node.has_children() {
            let children = node.enumerate_children()?;

            for (_, child_ptr) in children {
                if let Some(cell_index) = child_ptr.location().cell_index() {
                    self.delete_subtrie(context, slotted_page, cell_index)?
                } else {
                    // the child is a root of another page, and that child will be
                    // deleted, essentially orphaning that page and all descendants of
                    // that page.
                    let page_id = child_ptr.location().page_id().expect("page_id must exist");
                    let page = self.get_page(context, page_id)?;
                    let slotted_page = SlottedPage::try_from(page)?;
                    self.orphan_subtrie(context, &slotted_page, 0)?
                }
            }
        }

        slotted_page.delete_value(cell_index)?;
        Ok(())
    }

    /// Orphans a subtrie from the page, orphaning any pages that become fully
    /// unreferenced as a result.
    ///
    /// Unlike delete_subtrie, this doesn't delete individual cells - it just marks
    /// entire pages as orphaned for eventual reuse.
    pub(super) fn orphan_subtrie(
        &self,
        context: &mut TransactionContext,
        slotted_page: &SlottedPage<'_>,
        cell_index: u8,
    ) -> Result<(), Error> {
        let node: Node = slotted_page.get_value(cell_index)?;

        if node.has_children() {
            let children = node.enumerate_children()?;

            for (_, child_ptr) in children {
                if let Some(cell_index) = child_ptr.location().cell_index() {
                    self.orphan_subtrie(context, slotted_page, cell_index)?;
                } else {
                    // the child is a root of another page, and that child will be
                    // deleted, essentially orphaning that page and all descendants of
                    // that page.
                    let child_page = self.get_page(
                        context,
                        child_ptr.location().page_id().expect("page_id must exist"),
                    )?;
                    let child_slotted_page = SlottedPage::try_from(child_page)?;
                    self.orphan_subtrie(context, &child_slotted_page, 0)?
                }
            }
        }

        if cell_index == 0 {
            self.orphan_page(context, slotted_page.id())?;
        }

        Ok(())
    }
}
