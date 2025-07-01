use std::{error, fmt, io};

#[derive(Debug)]
pub struct CorruptedMetadataError;

impl fmt::Display for CorruptedMetadataError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "corrupted metadata")
    }
}

impl error::Error for CorruptedMetadataError {}

#[derive(Debug)]
pub enum OpenMetadataError {
    Corrupted,
    IO(io::Error),
}

impl Clone for OpenMetadataError {
    fn clone(&self) -> Self {
        match self {
            Self::Corrupted => Self::Corrupted,
            Self::IO(e) => Self::IO(std::io::Error::new(e.kind(), e.to_string())),
        }
    }
}

impl fmt::Display for OpenMetadataError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Corrupted => write!(f, "corrupted metadata"),
            Self::IO(ref e) => write!(f, "I/O error: {e}"),
        }
    }
}

impl error::Error for OpenMetadataError {}

impl From<CorruptedMetadataError> for OpenMetadataError {
    fn from(_: CorruptedMetadataError) -> Self {
        Self::Corrupted
    }
}

impl From<io::Error> for OpenMetadataError {
    fn from(e: io::Error) -> Self {
        Self::IO(e)
    }
}
