use crate::{
    buffer::CryptoBuffer,
    parse_buffer::{ParseBuffer, ParseError},
    TlsError,
};

mod extension_group_macro;

pub mod extension_data;
pub mod messages;

#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum ExtensionType {
    ServerName = 0,
    MaxFragmentLength = 1,
    StatusRequest = 5,
    SupportedGroups = 10,
    SignatureAlgorithms = 13,
    UseSrtp = 14,
    Heartbeat = 15,
    ApplicationLayerProtocolNegotiation = 16,
    SignedCertificateTimestamp = 18,
    ClientCertificateType = 19,
    ServerCertificateType = 20,
    Padding = 21,
    PreSharedKey = 41,
    EarlyData = 42,
    SupportedVersions = 43,
    Cookie = 44,
    PskKeyExchangeModes = 45,
    CertificateAuthorities = 47,
    OidFilters = 48,
    PostHandshakeAuth = 49,
    SignatureAlgorithmsCert = 50,
    KeyShare = 51,
}

impl ExtensionType {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        match buf.read_u16()? {
            v if v == Self::ServerName as u16 => Ok(Self::ServerName),
            v if v == Self::MaxFragmentLength as u16 => Ok(Self::MaxFragmentLength),
            v if v == Self::StatusRequest as u16 => Ok(Self::StatusRequest),
            v if v == Self::SupportedGroups as u16 => Ok(Self::SupportedGroups),
            v if v == Self::SignatureAlgorithms as u16 => Ok(Self::SignatureAlgorithms),
            v if v == Self::UseSrtp as u16 => Ok(Self::UseSrtp),
            v if v == Self::Heartbeat as u16 => Ok(Self::Heartbeat),
            v if v == Self::ApplicationLayerProtocolNegotiation as u16 => {
                Ok(Self::ApplicationLayerProtocolNegotiation)
            }
            v if v == Self::SignedCertificateTimestamp as u16 => {
                Ok(Self::SignedCertificateTimestamp)
            }
            v if v == Self::ClientCertificateType as u16 => Ok(Self::ClientCertificateType),
            v if v == Self::ServerCertificateType as u16 => Ok(Self::ServerCertificateType),
            v if v == Self::Padding as u16 => Ok(Self::Padding),
            v if v == Self::PreSharedKey as u16 => Ok(Self::PreSharedKey),
            v if v == Self::EarlyData as u16 => Ok(Self::EarlyData),
            v if v == Self::SupportedVersions as u16 => Ok(Self::SupportedVersions),
            v if v == Self::Cookie as u16 => Ok(Self::Cookie),
            v if v == Self::PskKeyExchangeModes as u16 => Ok(Self::PskKeyExchangeModes),
            v if v == Self::CertificateAuthorities as u16 => Ok(Self::CertificateAuthorities),
            v if v == Self::OidFilters as u16 => Ok(Self::OidFilters),
            v if v == Self::PostHandshakeAuth as u16 => Ok(Self::PostHandshakeAuth),
            v if v == Self::SignatureAlgorithmsCert as u16 => Ok(Self::SignatureAlgorithmsCert),
            v if v == Self::KeyShare as u16 => Ok(Self::KeyShare),
            other => {
                warn!("Read unknown ExtensionType: {}", other);
                Err(ParseError::InvalidData)
            }
        }
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        buf.push_u16(*self as u16)
            .map_err(|_| TlsError::EncodeError)
    }
}
