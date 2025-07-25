use std::{error::Error, fmt};

#[derive(Debug)]
pub enum TransactionError {
    /// Generic transaction error (for backward compatibility)
    Generic,
    /// Overlay functionality is not enabled for this transaction
    OverlayNotEnabled,
}

impl fmt::Display for TransactionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Generic => write!(f, "transaction error"),
            Self::OverlayNotEnabled => write!(f, "overlay functionality is not enabled for this transaction"),
        }
    }
}

impl Error for TransactionError {}
