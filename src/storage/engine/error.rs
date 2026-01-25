//! Error types for storage engine operations.

use crate::{node::NodeError, page::PageError};
use std::io;
use thiserror::Error;

/// Errors that can occur during storage engine operations.
#[derive(Debug, Error)]
pub enum Error {
    /// I/O error from underlying storage.
    #[error("I/O error: {0}")]
    IO(#[from] io::Error),
    /// Error operating on trie nodes.
    #[error("Node error: {0}")]
    NodeError(#[from] NodeError),
    /// Error operating on pages.
    #[error("Page error: {0}")]
    PageError(#[from] PageError),
    /// Invalid common prefix index during trie traversal.
    #[error("Invalid common prefix index")]
    InvalidCommonPrefixIndex,
    /// Invalid snapshot ID for the operation.
    #[error("Invalid snapshot ID")]
    InvalidSnapshotId,
    /// Page split required; contains count of changes already processed.
    #[error("Page split required after {0} changes")]
    PageSplit(usize),
    /// Debug operation error.
    #[error("Debug error: {0}")]
    DebugError(String),
    /// Proof generation error.
    #[error("Proof error: {0}")]
    ProofError(String),
}
