use crate::{
    buffer::CryptoBuffer,
    parse_buffer::{ParseBuffer, ParseError},
    TlsError,
};
use heapless::Vec;

#[derive(Clone, Copy, PartialEq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct ProtocolVersion(u16);

impl ProtocolVersion {
    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        buf.push_u16(self.0).map_err(|_| TlsError::EncodeError)
    }

    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        buf.read_u16().map(Self)
    }
}

pub const TLS13: ProtocolVersion = ProtocolVersion(0x0304);

#[derive(Debug, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct SupportedVersionsClientHello<const N: usize> {
    pub versions: Vec<ProtocolVersion, N>,
}

impl<const N: usize> SupportedVersionsClientHello<N> {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        let data_length = buf.read_u8()? as usize;

        Ok(Self {
            versions: buf.read_list::<_, N>(data_length, ProtocolVersion::parse)?,
        })
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        buf.with_u8_length(|buf| {
            for v in self.versions.iter() {
                v.encode(buf)?;
            }
            Ok(())
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct SupportedVersionsServerHello {
    pub selected_version: ProtocolVersion,
}

impl SupportedVersionsServerHello {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        Ok(Self {
            selected_version: ProtocolVersion::parse(buf)?,
        })
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        self.selected_version.encode(buf)
    }
}
