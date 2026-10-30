use crate::extensions::extension_data::signature_algorithms::SignatureScheme;
use crate::parse_buffer::ParseBuffer;
use crate::TlsError;

#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct CertificateVerify<'a> {
    pub(crate) signature_scheme: SignatureScheme,
    pub(crate) signature: &'a [u8],
}

impl<'a> CertificateVerify<'a> {
    pub fn parse(buf: &mut ParseBuffer<'a>) -> Result<CertificateVerify<'a>, TlsError> {
        let signature_scheme =
            SignatureScheme::parse(buf).map_err(|_| TlsError::InvalidSignatureScheme)?;

        let len = buf.read_u16().map_err(|_| TlsError::InvalidSignature)?;
        let signature = buf
            .slice(len as usize)
            .map_err(|_| TlsError::InvalidSignature)?;

        Ok(Self {
            signature_scheme,
            signature: signature.as_slice(),
        })
    }
}
