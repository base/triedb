//! Read operations for the storage engine.
//!
//! This module contains functions for reading accounts and storage values
//! from the trie structure.

use super::{Error, StorageEngine};
use crate::{
    account::Account,
    context::TransactionContext,
    node::{
        Node,
        NodeKind::{AccountLeaf, Branch},
        TrieValue,
    },
    page::SlottedPage,
    path::{AddressPath, RawPath, StoragePath, ADDRESS_PATH_LENGTH},
};
use alloy_primitives::StorageValue;
use alloy_trie::EMPTY_ROOT_HASH;

impl StorageEngine {
    /// Retrieves an [Account] from the storage engine, identified by the given [AddressPath].
    /// Returns [None] if the path is not found.
    pub fn get_account(
        &self,
        context: &mut TransactionContext,
        address_path: &AddressPath,
    ) -> Result<Option<Account>, Error> {
        match context.root_node_page_id {
            None => Ok(None),
            Some(root_node_page_id) => {
                let page = self.get_page(context, root_node_page_id)?;
                let slotted_page = SlottedPage::try_from(page)?;
                match self.get_value_from_page(context, &address_path.into(), 0, slotted_page, 0)? {
                    Some(TrieValue::Account(account)) => Ok(Some(account)),
                    _ => Ok(None),
                }
            }
        }
    }

    /// Retrieves a [StorageValue] from the storage engine, identified by the given [StoragePath].
    /// Returns [None] if the path is not found.
    pub fn get_storage(
        &self,
        context: &mut TransactionContext,
        storage_path: &StoragePath,
    ) -> Result<Option<StorageValue>, Error> {
        let root_node_page_id = match context.root_node_page_id {
            None => return Ok(None),
            Some(page_id) => page_id,
        };

        // check the cache
        let nibbles = storage_path.get_address().into();
        let cache_location = context.contract_account_loc_cache.get(&nibbles);
        let (slotted_page, page_index, path_offset) = match cache_location {
            Some((page_id, page_index)) => {
                context.transaction_metrics.inc_cache_storage_read_hit();

                let path_offset = storage_path.get_slot_offset();
                // read the current account
                let page = self.get_page(context, page_id)?;
                let slotted_page = SlottedPage::try_from(page)?;
                let node: Node = slotted_page.get_value(page_index)?;
                let child_pointer = node.direct_child()?;
                // only when the node is an account leaf and all storage slots are removed
                if child_pointer.is_none() {
                    return Ok(None);
                }
                let child_location = child_pointer.unwrap().location();
                let (slotted_page, page_index) = if child_location.cell_index().is_some() {
                    (slotted_page, child_location.cell_index().unwrap())
                } else {
                    let child_page_id = child_location.page_id().unwrap();
                    let child_page = self.get_page(context, child_page_id)?;
                    let child_slotted_page = SlottedPage::try_from(child_page)?;
                    (child_slotted_page, 0)
                };
                (slotted_page, page_index, path_offset)
            }
            None => {
                context.transaction_metrics.inc_cache_storage_read_miss();

                let page = self.get_page(context, root_node_page_id)?;
                let slotted_page = SlottedPage::try_from(page)?;
                (slotted_page, 0, 0)
            }
        };

        let original_path: RawPath = storage_path.into();

        match self.get_value_from_page(
            context,
            &original_path,
            path_offset,
            slotted_page,
            page_index,
        )? {
            Some(TrieValue::Storage(storage_value)) => Ok(Some(storage_value)),
            _ => Ok(None),
        }
    }

    /// Retrieves a [TrieValue] from the given page or any of its descendants.
    ///
    /// This is the core recursive function for traversing the trie to find a value.
    /// It handles all node types (AccountLeaf, StorageLeaf, Branch) and follows
    /// pointers to child nodes as needed.
    ///
    /// # Parameters
    /// - `context`: Transaction context for metrics and caching
    /// - `original_path`: The full path being searched for
    /// - `path_offset`: Current offset into the path (how much has been consumed)
    /// - `slotted_page`: The current page being searched
    /// - `page_index`: Cell index of the current node in the page
    ///
    /// # Returns
    /// - `Ok(Some(value))`: The value was found
    /// - `Ok(None)`: The path does not exist in the trie
    pub(super) fn get_value_from_page(
        &self,
        context: &mut TransactionContext,
        original_path: &RawPath,
        path_offset: usize,
        slotted_page: SlottedPage<'_>,
        page_index: u8,
    ) -> Result<Option<TrieValue>, Error> {
        let node: Node = slotted_page.get_value(page_index)?;

        let common_prefix_length =
            original_path.slice(path_offset..).common_prefix_length(&node.prefix().into());

        if common_prefix_length < node.prefix().len() {
            return Ok(None);
        }

        let remaining_path = original_path.slice(path_offset + common_prefix_length..);
        if remaining_path.is_empty() {
            // cache the account location if it is a contract account
            if let TrieValue::Account(account) = node.value()? {
                if account.storage_root != EMPTY_ROOT_HASH &&
                    original_path.len() == ADDRESS_PATH_LENGTH
                {
                    context
                        .contract_account_loc_cache
                        .insert(original_path, (slotted_page.id(), page_index));
                }
            }

            return Ok(Some(node.value()?));
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
                let child_location = child_pointer.location();
                if child_location.cell_index().is_some() {
                    self.get_value_from_page(
                        context,
                        original_path,
                        new_path_offset,
                        slotted_page,
                        child_location.cell_index().unwrap(),
                    )
                } else {
                    let child_page_id = child_location.page_id().unwrap();
                    let child_page = self.get_page(context, child_page_id)?;
                    let child_slotted_page = SlottedPage::try_from(child_page)?;
                    self.get_value_from_page(
                        context,
                        original_path,
                        new_path_offset,
                        child_slotted_page,
                        0,
                    )
                }
            }
            None => Ok(None),
        }
    }
}
