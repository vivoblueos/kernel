use crate::{
    buffer::CryptoBuffer,
    parse_buffer::{ParseBuffer, ParseError},
    TlsError,
};

use heapless::Vec;

#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum SignatureScheme {
    /* RSASSA-PKCS1-v1_5 algorithms */
    RsaPkcs1Sha256 = 0x0401,
    RsaPkcs1Sha384 = 0x0501,
    RsaPkcs1Sha512 = 0x0601,

    /* ECDSA algorithms */
    EcdsaSecp256r1Sha256 = 0x0403,
    EcdsaSecp384r1Sha384 = 0x0503,
    EcdsaSecp521r1Sha512 = 0x0603,

    /* RSASSA-PSS algorithms with public key OID rsaEncryption */
    RsaPssRsaeSha256 = 0x0804,
    RsaPssRsaeSha384 = 0x0805,
    RsaPssRsaeSha512 = 0x0806,

    /* EdDSA algorithms */
    Ed25519 = 0x0807,
    Ed448 = 0x0808,

    /* RSASSA-PSS algorithms with public key OID RSASSA-PSS */
    RsaPssPssSha256 = 0x0809,
    RsaPssPssSha384 = 0x080a,
    RsaPssPssSha512 = 0x080b,

    /* Legacy algorithms */
    RsaPkcs1Sha1 = 0x0201,
    EcdsaSha1 = 0x0203,
    /* Reserved Code Points */
    //private_use(0xFE00..0xFFFF),
    //(0xFFFF)
}

impl SignatureScheme {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        match buf.read_u16()? {
            0x0401 => Ok(Self::RsaPkcs1Sha256),
            0x0501 => Ok(Self::RsaPkcs1Sha384),
            0x0601 => Ok(Self::RsaPkcs1Sha512),

            0x0403 => Ok(Self::EcdsaSecp256r1Sha256),
            0x0503 => Ok(Self::EcdsaSecp384r1Sha384),
            0x0603 => Ok(Self::EcdsaSecp521r1Sha512),

            0x0804 => Ok(Self::RsaPssRsaeSha256),
            0x0805 => Ok(Self::RsaPssRsaeSha384),
            0x0806 => Ok(Self::RsaPssRsaeSha512),

            0x0807 => Ok(Self::Ed25519),
            0x0808 => Ok(Self::Ed448),

            0x0809 => Ok(Self::RsaPssPssSha256),
            0x080a => Ok(Self::RsaPssPssSha384),
            0x080b => Ok(Self::RsaPssPssSha512),

            0x0201 => Ok(Self::RsaPkcs1Sha1),
            0x0203 => Ok(Self::EcdsaSha1),
            _ => Err(ParseError::InvalidData),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct SignatureAlgorithms<const N: usize> {
    pub supported_signature_algorithms: Vec<SignatureScheme, N>,
}

impl<const N: usize> SignatureAlgorithms<N> {
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
