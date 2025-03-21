use std::{error::Error, fmt};

#[derive(Debug)]
pub struct TransactionError;

impl fmt::Display for TransactionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "transaction error")
    }
}

impl Error for TransactionError {}
