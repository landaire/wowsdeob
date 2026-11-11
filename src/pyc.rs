use crate::error::UnpackError;

/// The `.pyc` magic number, which identifies the bytecode version.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PycMagic(pub u32);

/// The source modification timestamp stored in a `.pyc` header.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModDate(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PycHeader {
    pub magic: PycMagic,
    pub moddate: ModDate,
}

impl PycHeader {
    pub const LEN: usize = 8;

    /// Splits a `.pyc` file into its header and the marshalled body that follows it.
    pub fn parse(pyc: &[u8]) -> Result<(Self, &[u8]), UnpackError> {
        let Some((header, body)) = pyc.split_first_chunk::<{ Self::LEN }>() else {
            return Err(UnpackError::TruncatedHeader { len: pyc.len() });
        };

        let [m0, m1, m2, m3, d0, d1, d2, d3] = *header;
        let header = Self {
            magic: PycMagic(u32::from_le_bytes([m0, m1, m2, m3])),
            moddate: ModDate(u32::from_le_bytes([d0, d1, d2, d3])),
        };

        Ok((header, body))
    }

    pub fn to_bytes(self) -> [u8; Self::LEN] {
        let [m0, m1, m2, m3] = self.magic.0.to_le_bytes();
        let [d0, d1, d2, d3] = self.moddate.0.to_le_bytes();

        [m0, m1, m2, m3, d0, d1, d2, d3]
    }
}
