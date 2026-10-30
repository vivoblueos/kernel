use heapless::Vec;

use crate::{
    buffer::CryptoBuffer,
    parse_buffer::{ParseBuffer, ParseError},
    TlsError,
};

#[derive(Copy, Clone, Debug, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[repr(u16)]
pub enum NamedGroup {
    /* Elliptic Curve Groups (ECDHE) */
    Secp256r1 = 0x0017,
    Secp384r1 = 0x0018,
    Secp521r1 = 0x0019,
    X25519 = 0x001D,
    X448 = 0x001E,

    /* Finite Field Groups (DHE) */
    Ffdhe2048 = 0x0100,
    Ffdhe3072 = 0x0101,
    Ffdhe4096 = 0x0102,
    Ffdhe6144 = 0x0103,
    Ffdhe8192 = 0x0104,

    Unknown(u16),
}

impl NamedGroup {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        let v = buf.read_u16()?;
        match v {
            0x0017 => Ok(Self::Secp256r1),
            0x0018 => Ok(Self::Secp384r1),
            0x0019 => Ok(Self::Secp521r1),
            0x001D => Ok(Self::X25519),
            0x001E => Ok(Self::X448),
            0x0100 => Ok(Self::Ffdhe2048),
            0x0101 => Ok(Self::Ffdhe3072),
            0x0102 => Ok(Self::Ffdhe4096),
            0x0103 => Ok(Self::Ffdhe6144),
            0x0104 => Ok(Self::Ffdhe8192),
            v => Ok(Self::Unknown(v)),
        }
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        let val = match self {
            Self::Unknown(v) => *v,
            Self::Secp256r1 => 0x0017,
            Self::Secp384r1 => 0x0018,
            Self::Secp521r1 => 0x0019,
            Self::X25519 => 0x001D,
            Self::X448 => 0x001E,
            Self::Ffdhe2048 => 0x0100,
            Self::Ffdhe3072 => 0x0101,
            Self::Ffdhe4096 => 0x0102,
            Self::Ffdhe6144 => 0x0103,
            Self::Ffdhe8192 => 0x0104,
        };
        buf.push_u16(val)
            .map_err(|_| TlsError::EncodeError)
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct SupportedGroups<const N: usize> {
    pub supported_groups: Vec<NamedGroup, N>,
}

impl<const N: usize> SupportedGroups<N> {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        let data_length = buf.read_u16()? as usize;

        Ok(Self {
            supported_groups: buf.read_list::<_, N>(data_length, NamedGroup::parse)?,
        })
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        buf.with_u16_length(|buf| {
            for g in self.supported_groups.iter() {
                g.encode(buf)?;
            }
            Ok(())
        })
    }
}
