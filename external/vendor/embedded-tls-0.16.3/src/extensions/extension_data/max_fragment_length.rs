use crate::{
    buffer::CryptoBuffer,
    parse_buffer::{ParseBuffer, ParseError},
    TlsError,
};

/// Maximum plaintext fragment length
///
/// RFC 6066, Section 4.  Maximum Fragment Length Negotiation
/// Without this extension, TLS specifies a fixed maximum plaintext
/// fragment length of 2^14 bytes.  It may be desirable for constrained
/// clients to negotiate a smaller maximum fragment length due to memory
/// limitations or bandwidth limitations.
#[derive(Debug, Copy, Clone, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum MaxFragmentLength {
    /// 512 bytes
    Bits9 = 1,
    /// 1024 bytes
    Bits10 = 2,
    /// 2048 bytes
    Bits11 = 3,
    /// 4096 bytes
    Bits12 = 4,
}

impl MaxFragmentLength {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        match buf.read_u8()? {
            1 => Ok(Self::Bits9),
            2 => Ok(Self::Bits10),
            3 => Ok(Self::Bits11),
            4 => Ok(Self::Bits12),
            other => {
                warn!("Read unknown MaxFragmentLength: {}", other);
                Err(ParseError::InvalidData)
            }
        }
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        buf.push(*self as u8).map_err(|_| TlsError::EncodeError)
    }
}
