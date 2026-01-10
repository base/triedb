//! Error types for storage engine operations.

use crate::{node::NodeError, page::PageError};
use std::io;

/// Errors that can occur during storage engine operations.
#[derive(Debug)]
pub enum Error {
    /// I/O error from underlying storage.
    IO(io::Error),
    /// Error operating on trie nodes.
    NodeError(NodeError),
    /// Error operating on pages.
    PageError(PageError),
    /// Invalid common prefix index during trie traversal.
    InvalidCommonPrefixIndex,
    /// Invalid snapshot ID for the operation.
    InvalidSnapshotId,
    /// Page split required; contains count of changes already processed.
    PageSplit(usize),
    /// Debug operation error.
    DebugError(String),
    /// Proof generation error.
    ProofError(String),
}

impl From<PageError> for Error {
    fn from(error: PageError) -> Self {
        Self::PageError(error)
    }
}

impl From<NodeError> for Error {
    fn from(error: NodeError) -> Self {
        Self::NodeError(error)
    }
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Self::IO(error)
    }
}
