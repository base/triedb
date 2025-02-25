use std::fmt::Debug;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
pub enum Error {
    InvalidEncoding,
}

/// A trait for types that can be stored as values in the database
pub trait Value: Sized + Debug {
    /// Convert this value into a byte vec for storage
    fn to_bytes(self) -> Vec<u8>;

    /// Create a value from a byte slice
    /// Returns Error::InvalidEncoding if the bytes don't represent a valid value
    fn from_bytes(bytes: &[u8]) -> Result<Self>;
}

/// A trait for references to values stored in the database
/// The lifetime parameter represents how long the reference is valid
pub trait ValueRef<'v>: Sized + Debug {
    /// The owned version of this value
    type Owned: Value;

    /// Convert this reference into a byte slice
    fn to_bytes(self) -> &'v [u8];

    /// Create a reference from a byte slice
    /// Returns Error::InvalidEncoding if the bytes don't represent a valid value
    fn from_bytes(bytes: &'v [u8]) -> Result<Self>;

    /// Convert this reference into an owned value
    fn to_owned(self) -> Self::Owned;
}

// Example implementation for a string-like type
impl Value for String {
    fn to_bytes(self) -> Vec<u8> {
        self.into_bytes()
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self> {
        let s = String::from_utf8(bytes.to_vec()).map_err(|_| Error::InvalidEncoding)?;
        Ok(s)
    }
}

// Example of a reference type implementation
impl<'v> ValueRef<'v> for &'v str {
    type Owned = String;

    fn to_bytes(self) -> &'v [u8] {
        self.as_bytes()
    }

    fn from_bytes(bytes: &'v [u8]) -> Result<Self> {
        let s = std::str::from_utf8(bytes).map_err(|_| Error::InvalidEncoding)?;
        Ok(s)
    }

    fn to_owned(self) -> Self::Owned {
        String::from(self)
    }
}

// Example implementation for a vector of bytes, useful for testing purposes
impl Value for Vec<u8> {
    fn to_bytes(self) -> Vec<u8> {
        self
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self> {
        Ok(bytes.to_vec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_string_value() {
        let s = String::from("hello");
        let bytes: Vec<u8> = s.clone().into();
        let parsed = String::from_bytes(&bytes).unwrap();
        assert_eq!(s, parsed);
    }

    #[test]
    fn test_string_ref() {
        let original = String::from("hello");
        let bytes: &[u8] = original.as_bytes();

        // Create reference type
        let string_ref: &str = ValueRef::from_bytes(bytes).unwrap();

        // Convert to owned
        let owned = ValueRef::to_owned(string_ref);
        assert_eq!(owned, original);
    }

    #[test]
    fn test_string_ref_conversion() {
        let s = String::from("hello");
        let s_ref = AsRef::as_ref(&s);
        assert_eq!(ValueRef::to_owned(s_ref), s);
    }
}
