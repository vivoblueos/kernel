use crate::parse_buffer::{ParseBuffer, ParseError};

#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum CipherSuite {
    TlsAes128GcmSha256 = 0x1301,
    TlsAes256GcmSha384 = 0x1302,
    TlsChacha20Poly1305Sha256 = 0x1303,
    TlsAes128CcmSha256 = 0x1304,
    TlsAes128Ccm8Sha256 = 0x1305,
    TlsPskAes128GcmSha256 = 0x00A8,
}

impl CipherSuite {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        match buf.read_u16()? {
            v if v == Self::TlsAes128GcmSha256 as u16 => Ok(Self::TlsAes128GcmSha256),
            v if v == Self::TlsAes256GcmSha384 as u16 => Ok(Self::TlsAes256GcmSha384),
            v if v == Self::TlsChacha20Poly1305Sha256 as u16 => Ok(Self::TlsChacha20Poly1305Sha256),
            v if v == Self::TlsAes128CcmSha256 as u16 => Ok(Self::TlsAes128CcmSha256),
            v if v == Self::TlsAes128Ccm8Sha256 as u16 => Ok(Self::TlsAes128Ccm8Sha256),
            v if v == Self::TlsPskAes128GcmSha256 as u16 => Ok(Self::TlsPskAes128GcmSha256),
            _ => Err(ParseError::InvalidData),
        }
    }
}
