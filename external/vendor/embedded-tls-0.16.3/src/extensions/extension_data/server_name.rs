use heapless::Vec;

use crate::{
    buffer::CryptoBuffer,
    extensions::ExtensionType,
    parse_buffer::{ParseBuffer, ParseError},
    TlsError,
};

#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum NameType {
    HostName = 0,
}

impl NameType {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        match buf.read_u8()? {
            0 => Ok(Self::HostName),
            other => {
                warn!("Read unknown NameType: {}", other);
                Err(ParseError::InvalidData)
            }
        }
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        buf.push(*self as u8).map_err(|_| TlsError::EncodeError)
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct ServerName<'a> {
    pub name_type: NameType,
    pub name: &'a str,
}

impl<'a> ServerName<'a> {
    pub fn parse(buf: &mut ParseBuffer<'a>) -> Result<ServerName<'a>, ParseError> {
        let name_type = NameType::parse(buf)?;
        let name_len = buf.read_u16()?;
        let name = buf.slice(name_len as usize)?.as_slice();

        // RFC 6066, Section 3.  Server Name Indication
        // The hostname is represented as a byte
        // string using ASCII encoding without a trailing dot.
        if name.is_ascii() {
            Ok(ServerName {
                name_type,
                name: core::str::from_utf8(name).map_err(|_| ParseError::InvalidData)?,
            })
        } else {
            Err(ParseError::InvalidData)
        }
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        self.name_type.encode(buf)?;

        buf.with_u16_length(|buf| buf.extend_from_slice(self.name.as_bytes()))
            .map_err(|_| TlsError::EncodeError)
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct ServerNameList<'a, const N: usize> {
    pub names: Vec<ServerName<'a>, N>,
}

impl<'a> ServerNameList<'a, 1> {
    pub fn single(server_name: &'a str) -> Self {
        let mut names = Vec::<_, 1>::new();

        names
            .push(ServerName {
                name_type: NameType::HostName,
                name: server_name,
            })
            .unwrap();

        ServerNameList { names }
    }
}

impl<'a, const N: usize> ServerNameList<'a, N> {
    pub const EXTENSION_TYPE: ExtensionType = ExtensionType::ServerName;

    pub fn parse(buf: &mut ParseBuffer<'a>) -> Result<ServerNameList<'a, N>, ParseError> {
        let data_length = buf.read_u16()? as usize;

        Ok(Self {
            names: buf.read_list::<_, N>(data_length, ServerName::parse)?,
        })
    }

    pub fn encode(&self, buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        buf.with_u16_length(|buf| {
            for name in self.names.iter() {
                name.encode(buf)?;
            }

            Ok(())
        })
    }
}

// RFC 6066, Section 3.  Server Name Indication
// A server that receives a client hello containing the "server_name"
// extension [..].  In this event, the server
// SHALL include an extension of type "server_name" in the (extended)
// server hello.  The "extension_data" field of this extension SHALL be
// empty.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct ServerNameResponse;

impl ServerNameResponse {
    pub fn parse(buf: &mut ParseBuffer) -> Result<Self, ParseError> {
        if !buf.is_empty() {
            Err(ParseError::InvalidData)
        } else {
            Ok(Self)
        }
    }

    pub fn encode(&self, _buf: &mut CryptoBuffer) -> Result<(), TlsError> {
        Ok(())
    }
}
