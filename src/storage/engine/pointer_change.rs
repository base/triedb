//! Pointer change tracking for trie modifications.

use crate::pointer::Pointer;

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
