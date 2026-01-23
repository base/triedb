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

mod engine;
mod error;
mod handlers;
mod helpers;
mod page_ops;
mod pointer_change;
mod read;
mod write;

pub use engine::StorageEngine;
pub use error::Error;

pub(crate) use pointer_change::PointerChange;

#[cfg(test)]
mod tests;
