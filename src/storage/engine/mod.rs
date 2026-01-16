//! Storage engine for the trie database.
//!
//! The [StorageEngine] is responsible for managing the storage of data in the database.
//! It handles reading and writing account and storage values, as well as managing the
//! lifecycle of pages.
//!
//! ## Module Organization
//!
//! The storage engine is split into several submodules for maintainability:
//!
//! - [`error`]: Error types for storage operations
//! - [`read`]: Read operations (get_account, get_storage)
//! - [`write`]: Write operations (set_values)
//! - [`handlers`]: Trie modification handlers (branch/leaf operations)
//! - [`page_ops`]: Page-level operations (allocate, orphan, split)
//! - [`helpers`]: Utility functions (prefix matching, subtrie operations)
//!
//! ## Architecture
//!
//! The storage engine uses a copy-on-write (CoW) approach with MVCC for concurrency:
//! - Updates copy pages to new locations
//! - Root pointer is only updated after fsync
//! - Single writer, multiple concurrent readers
//!
//! Pages are organized as a 4KB slotted page format, with nodes stored in cells
//! and pointers linking them together into the trie structure.

mod error;
mod handlers;
mod helpers;
mod page_ops;
mod read;
mod write;

pub use error::Error;

use crate::{
    context::TransactionContext, meta::MetadataManager, page::PageManager, pointer::Pointer,
    snapshot::SnapshotId,
};
use parking_lot::Mutex;
use rayon::ThreadPool;
use std::{
    fmt::Debug,
    io,
    sync::atomic::{AtomicU64, Ordering},
};

/// The [StorageEngine] is responsible for managing the storage of data in the database.
/// It handles reading and writing account and storage values, as well as managing the lifecycle of
/// pages.
///
/// The storage engine uses a [PageManager] to interact with the underlying storage medium,
/// which could be memory-mapped files, in-memory storage, or other implementations.
#[derive(Debug)]
pub struct StorageEngine {
    pub(crate) page_manager: PageManager,
    pub(crate) meta_manager: Mutex<MetadataManager>,
    pub(crate) alive_snapshot: AtomicU64,
    #[allow(dead_code)]
    thread_pool: ThreadPool,
}

/// Represents a change to a node pointer during trie modification.
#[derive(Debug)]
pub(crate) enum PointerChange {
    /// No change occurred
    None,
    /// Pointer was updated to a new value
    Update(Pointer),
    /// Node was deleted
    Delete,
}

impl StorageEngine {
    /// Creates a new StorageEngine with the given page manager, metadata manager, and thread pool.
    pub fn new(
        page_manager: PageManager,
        meta_manager: MetadataManager,
        thread_pool: ThreadPool,
    ) -> Self {
        let alive_snapshot = meta_manager.active_slot().snapshot_id();
        Self {
            page_manager,
            meta_manager: Mutex::new(meta_manager),
            alive_snapshot: AtomicU64::new(alive_snapshot),
            thread_pool,
        }
    }

    /// Closes the storage engine, flushing all data to disk.
    pub fn close(self) -> io::Result<()> {
        let Self { page_manager, meta_manager, .. } = self;
        page_manager.close()?;
        meta_manager.into_inner().close()?;
        Ok(())
    }

    /// Returns a [`TransactionContext`] valid for reads.
    ///
    /// The returned context points to the latest committed snapshot.
    pub(crate) fn read_context(&self) -> TransactionContext {
        let meta_manager = self.meta_manager.lock();
        let meta = meta_manager.active_slot();
        TransactionContext::new(meta)
    }

    /// Returns a [`TransactionContext`] valid for writes.
    ///
    /// The returned context points to the latest uncommitted snapshot.
    pub(crate) fn write_context(&self) -> TransactionContext {
        let meta_manager = self.meta_manager.lock();
        let meta = meta_manager.dirty_slot();
        TransactionContext::new(meta)
    }

    /// Unlocks any orphaned pages as of the given [SnapshotId] for reuse.
    pub(crate) fn unlock(&self, snapshot_id: SnapshotId) {
        self.alive_snapshot.store(snapshot_id + 1, Ordering::Relaxed);
    }

    /// Rolls back all outstanding data. Currently a no-op.
    pub fn rollback(&self, _context: &TransactionContext) -> Result<(), Error> {
        Ok(())
    }

    /// Returns the total number of pages in the storage engine.
    pub fn size(&self) -> u32 {
        self.page_manager.size()
    }

    /// Returns a StorageDebugger for examining the internal structure of the storage engine.
    pub fn debugger(&self) -> crate::storage::debug::StorageDebugger<'_> {
        crate::storage::debug::StorageDebugger::new(&self.page_manager)
    }
}

#[cfg(test)]
mod tests;
