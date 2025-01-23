use std::fmt::Debug;

pub trait Value: Debug + Clone + Default {
    fn as_bytes(&self) -> Vec<u8>;
    fn from_bytes(data: &[u8]) -> Self;
    // TODO: add method for RLP encoding
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StringValue(String);

impl Value for StringValue {
    fn as_bytes(&self) -> Vec<u8> {
        self.0.as_bytes().to_vec()
    }

    fn from_bytes(data: &[u8]) -> Self {
        let value = String::from_utf8(data.to_vec()).unwrap();
        Self(value)
    }
}

impl From<String> for StringValue {
    fn from(value: String) -> Self {
        // left-pad the string to 32 bytes
        let mut data = vec![0u8; 32];
        data[32 - value.len()..].copy_from_slice(value.as_bytes());
        let str = String::from_utf8(data).unwrap();
        Self(str)
    }
}