use crate::extensions::messages::EncryptedExtensionsExtension;

use crate::parse_buffer::ParseBuffer;
use crate::TlsError;
use heapless::Vec;

#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct EncryptedExtensions<'a> {
    extensions: Vec<EncryptedExtensionsExtension<'a>, 16>,
}

impl<'a> EncryptedExtensions<'a> {
    pub fn parse(buf: &mut ParseBuffer<'a>) -> Result<EncryptedExtensions<'a>, TlsError> {
        EncryptedExtensionsExtension::parse_vector(buf).map(|extensions| Self { extensions })
    }
}
