use crate::value::{Value, Error};
use alloy_rlp::Encodable;
use bytes::buf::BufMut;

#[derive(Debug, PartialEq, Eq)]
pub struct StorageSlot<'v>(&'v [u8]);

impl<'v> Value<'v> for StorageSlot<'v> {
    #[inline]
    fn as_bytes(&self) -> &'v [u8] {
        self.0
    }

    #[inline]
    fn try_from_bytes(data: &'v [u8]) -> Result<Self, Error> {
        if data.len() != 32 {
            return Err(Error::InvalidLength);
        }
        Ok(Self(data))
    }
}

impl<'v> Encodable for StorageSlot<'v> {
    #[inline]
    fn length(&self) -> usize {
        33
    }

    #[inline]
    fn encode(&self, out: &mut dyn BufMut) {
        out.put_u8(0xa0);
        out.put_slice(self.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_as_from_bytes() {
        let data = [42u8; 32];
        let slot = StorageSlot::try_from_bytes(&data).unwrap();
        assert_eq!(slot.as_bytes(), &data);
    }

    #[test]
    fn test_try_from_bytes_invalid_length() {
        let data = [0u8; 0];
        let result = StorageSlot::try_from_bytes(&data);
        assert!(result.is_err());

        let data = [42u8; 31];
        let result = StorageSlot::try_from_bytes(&data);
        assert!(result.is_err());

        let data = [42u8; 33];
        let result = StorageSlot::try_from_bytes(&data);
        assert!(result.is_err());
    }

    #[test]
    fn test_encode() {
        for data in [[0u8; 32], [42u8; 32], [255u8; 32]] {
            let slot = StorageSlot::try_from_bytes(&data).unwrap();
            let mut out = Vec::new();
            slot.encode(&mut out);
            assert_eq!(out, [&[0xa0][..], &data[..]].concat());

            // compare with the predefined byte slice encoding
            let mut out = Vec::new();
            slot.0.encode(&mut out);
            assert_eq!(out, [&[0xa0][..], &data[..]].concat());
        }
    }
}
