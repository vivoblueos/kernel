use crate::buffer::CryptoBuffer;

use crate::parse_buffer::{ParseBuffer, ParseError};
use crate::TlsError;

use heapless::Vec;

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct PreSharedKeyClientHello<'a, const N: usize> {
    pub identities: Vec<&'a [u8], N>,
    pub hash_size: usize,
}

impl<const N: usize> PreSharedKeyClientHello<'_, N> {
    pub fn parse(_buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        unimplemented!()
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        buf.with_u16_length(|buf| {
            for identity in self.identities.iter() {
                buf.with_u16_length(|buf| buf.extend_from_slice(identity))
                    .map_err(|_| TlsError::EncodeError)?;

                // NOTE: No support for ticket age, set to 0 as recommended by RFC
                buf.push_u32(0).map_err(|_| TlsError::EncodeError)?;
            }
            Ok(())
        })
        .map_err(|_| TlsError::EncodeError)?;

        // NOTE: We encode binders later after computing the transcript.
        let binders_len = (1 + self.hash_size) * self.identities.len();
        buf.push_u16(binders_len as u16)
            .map_err(|_| TlsError::EncodeError)?;

        for _ in 0..binders_len {
            buf.push(0).map_err(|_| TlsError::EncodeError)?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct PreSharedKeyServerHello {
    pub selected_identity: u16,
}

impl PreSharedKeyServerHello {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        Ok(Self {
            selected_identity: buf.read_u16()?,
        })
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        buf.push_u16(self.selected_identity)
            .map_err(|_| TlsError::EncodeError)
    }
}
