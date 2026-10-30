use crate::buffer::CryptoBuffer;

use crate::parse_buffer::{ParseBuffer, ParseError};
use crate::TlsError;

use heapless::Vec;

#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum PskKeyExchangeMode {
    PskKe = 0,
    PskDheKe = 1,
}
impl PskKeyExchangeMode {
    fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        match buf.read_u8()? {
            0 => Ok(Self::PskKe),
            1 => Ok(Self::PskDheKe),
            other => {
                warn!("Read unknown PskKeyExchangeMode: {}", other);
                Err(ParseError::InvalidData)
            }
        }
    }

    fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        buf.push(*self as u8).map_err(|_| TlsError::EncodeError)
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct PskKeyExchangeModes<const N: usize> {
    pub modes: Vec<PskKeyExchangeMode, N>,
}
impl<const N: usize> PskKeyExchangeModes<N> {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        let data_length = buf.read_u8()? as usize;

        Ok(Self {
            modes: buf.read_list::<_, N>(data_length, PskKeyExchangeMode::parse)?,
        })
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        buf.with_u8_length(|buf| {
            for mode in self.modes.iter() {
                mode.encode(buf)?;
            }
            Ok(())
        })
    }
}
