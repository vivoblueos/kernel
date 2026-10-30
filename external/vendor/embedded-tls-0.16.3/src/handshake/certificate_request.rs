use crate::extensions::messages::CertificateRequestExtension;
use crate::parse_buffer::ParseBuffer;
use crate::TlsError;
use heapless::Vec;

#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct CertificateRequestRef<'a> {
    pub(crate) request_context: &'a [u8],
}

impl<'a> CertificateRequestRef<'a> {
    pub fn parse(buf: &mut ParseBuffer<'a>) -> Result<CertificateRequestRef<'a>, TlsError> {
        let request_context_len = buf
            .read_u8()
            .map_err(|_| TlsError::InvalidCertificateRequest)?;
        let request_context = buf
            .slice(request_context_len as usize)
            .map_err(|_| TlsError::InvalidCertificateRequest)?;

        // Validate extensions
        CertificateRequestExtension::parse_vector::<6>(buf)?;

        Ok(Self {
            request_context: request_context.as_slice(),
        })
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct CertificateRequest {
    pub(crate) request_context: Vec<u8, 256>,
}

impl<'a> TryFrom<CertificateRequestRef<'a>> for CertificateRequest {
    type Error = TlsError;
    fn try_from(cert: CertificateRequestRef<'a>) -> Result<Self, Self::Error> {
        let mut request_context = Vec::new();
        request_context
            .extend_from_slice(cert.request_context)
            .map_err(|_| {
                error!("CertificateRequest: InsufficientSpace");
                TlsError::InsufficientSpace
            })?;
        Ok(Self { request_context })
    }
}
