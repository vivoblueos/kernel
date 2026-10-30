use crate::buffer::CryptoBuffer;
use crate::extensions::extension_data::signature_algorithms::SignatureScheme;

use crate::parse_buffer::{ParseBuffer, ParseError};
use crate::TlsError;

use heapless::Vec;

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct SignatureAlgorithmsCert<const N: usize> {
    pub supported_signature_algorithms: Vec<SignatureScheme, N>,
}

impl<const N: usize> SignatureAlgorithmsCert<N> {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        let data_length = buf.read_u16()? as usize;

        Ok(Self {
            supported_signature_algorithms: buf
                .read_list::<_, N>(data_length, SignatureScheme::parse)?,
        })
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        buf.with_u16_length(|buf| {
            for &a in self.supported_signature_algorithms.iter() {
                buf.push_u16(a as u16).map_err(|_| TlsError::EncodeError)?;
            }
            Ok(())
        })
    }
}
