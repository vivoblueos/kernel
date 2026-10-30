use crate::buffer::CryptoBuffer;
use crate::extensions::messages::CertificateExtension;
use crate::parse_buffer::ParseBuffer;
use crate::TlsError;
use heapless::Vec;

#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct CertificateRef<'a> {
    raw_entries: &'a [u8],
    request_context: &'a [u8],

    pub(crate) entries: Vec<CertificateEntryRef<'a>, 16>,
}

impl<'a> CertificateRef<'a> {
    pub fn with_context(request_context: &'a [u8]) -> Self {
        Self {
            raw_entries: &[],
            request_context,
            entries: Vec::new(),
        }
    }

    pub fn add(&mut self, entry: CertificateEntryRef<'a>) -> Result<(), TlsError> {
        self.entries.push(entry).map_err(|_| {
            error!("CertificateRef: InsufficientSpace");
            TlsError::InsufficientSpace
        })
    }

    pub fn parse(buf: &mut ParseBuffer<'a>) -> Result<Self, TlsError> {
        let request_context_len = buf.read_u8().map_err(|_| TlsError::InvalidCertificate)?;
        let request_context = buf
            .slice(request_context_len as usize)
            .map_err(|_| TlsError::InvalidCertificate)?;
        let entries_len = buf.read_u24().map_err(|_| TlsError::InvalidCertificate)?;
        let mut raw_entries = buf
            .slice(entries_len as usize)
            .map_err(|_| TlsError::InvalidCertificate)?;

        let entries = CertificateEntryRef::parse_vector(&mut raw_entries)?;

        Ok(Self {
            raw_entries: raw_entries.as_slice(),
            request_context: request_context.as_slice(),
            entries,
        })
    }

    pub(crate) fn encode(&self, buf: &mut CryptoBuffer<'_>) -> Result<(), TlsError> {
        buf.push(self.request_context.len() as u8)
            .map_err(|_| TlsError::EncodeError)?;
        buf.extend_from_slice(self.request_context)
            .map_err(|_| TlsError::EncodeError)?;

        buf.push_u24(self.entries.len() as u32)?;
        for entry in self.entries.iter() {
            entry.encode(buf)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum CertificateEntryRef<'a> {
    X509(&'a [u8]),
    RawPublicKey(&'a [u8]),
}

impl<'a> CertificateEntryRef<'a> {
    pub fn parse(buf: &mut ParseBuffer<'a>) -> Result<Self, TlsError> {
        let entry_len = buf
            .read_u24()
            .map_err(|_| TlsError::InvalidCertificateEntry)?;
        let cert = buf
            .slice(entry_len as usize)
            .map_err(|_| TlsError::InvalidCertificateEntry)?;

        let entry = CertificateEntryRef::X509(cert.as_slice());

        // Validate extensions
        CertificateExtension::parse_vector::<2>(buf)?;

        Ok(entry)
    }

    pub fn parse_vector<const N: usize>(
        buf: &mut ParseBuffer<'a>,
    ) -> Result<Vec<Self, N>, TlsError> {
        let mut result = Vec::new();

        while !buf.is_empty() {
            result
                .push(Self::parse(buf)?)
                .map_err(|_| TlsError::DecodeError)?;
        }

        Ok(result)
    }

    pub(crate) fn encode(&self, _buf: &mut CryptoBuffer<'_>) -> Result<(), TlsError> {
        todo!("not implemented");
        /*
        match self {
            CertificateEntry::RawPublicKey(key) => {
                let entry_len = (key.len() as u32).to_be_bytes();
            }
            CertificateEntry::X509(cert) => {
                let entry_len = (cert.len() as u32).to_be_bytes();
            }
        }
        Ok(())
        */
    }
}

impl<'a> From<&crate::config::Certificate<'a>> for CertificateEntryRef<'a> {
    fn from(cert: &crate::config::Certificate<'a>) -> Self {
        match cert {
            crate::config::Certificate::X509(data) => CertificateEntryRef::X509(data),
            crate::config::Certificate::RawPublicKey(data) => {
                CertificateEntryRef::RawPublicKey(data)
            }
        }
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct Certificate<const N: usize> {
    request_context: Vec<u8, 256>,
    num_entries: usize,
    entries_data: Vec<u8, N>,
}

impl<const N: usize> Certificate<N> {
    pub fn request_context(&self) -> &[u8] {
        &self.request_context[..]
    }
}

impl<'a, const N: usize> TryFrom<CertificateRef<'a>> for Certificate<N> {
    type Error = TlsError;
    fn try_from(cert: CertificateRef<'a>) -> Result<Self, Self::Error> {
        let mut request_context = Vec::new();
        request_context
            .extend_from_slice(cert.request_context)
            .map_err(|_| TlsError::OutOfMemory)?;
        let mut entries_data = Vec::new();
        entries_data
            .extend_from_slice(cert.raw_entries)
            .map_err(|_| TlsError::OutOfMemory)?;

        Ok(Self {
            request_context,
            num_entries: cert.entries.len(),
            entries_data,
        })
    }
}

impl<'a, const N: usize> TryFrom<&'a Certificate<N>> for CertificateRef<'a> {
    type Error = TlsError;
    fn try_from(cert: &'a Certificate<N>) -> Result<Self, Self::Error> {
        let request_context = cert.request_context();
        let entries =
            CertificateEntryRef::parse_vector(&mut ParseBuffer::from(&cert.entries_data[..]))?;
        Ok(Self {
            raw_entries: &cert.entries_data[..],
            request_context,
            entries,
        })
    }
}
