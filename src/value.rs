use std::fmt::Debug;

pub trait Value: Debug + Clone + Default {
    fn as_bytes(&self) -> Vec<u8>;
    fn from_bytes(data: &[u8]) -> Self;
    // TODO: add method for RLP encoding
}

impl Value for String {
    fn as_bytes(&self) -> Vec<u8> {
        self.as_bytes().to_vec()
    }

    fn from_bytes(data: &[u8]) -> Self {
        String::from_utf8(data.to_vec()).unwrap()
    }
}
