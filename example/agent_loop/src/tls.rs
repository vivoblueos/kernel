// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

extern crate embedded_tls;
use alloc::{format, string::String, vec, vec::Vec};
use core::fmt;
use embedded_io::{Error as _, ErrorKind, ErrorType, Read, Write};
use embedded_tls::blocking::*;
use rand_core::{CryptoRng, RngCore};
use std::net::TcpStream;

const TLS_READ_RECORD_BUF_SIZE: usize = 16640;
const TLS_WRITE_RECORD_BUF_SIZE: usize = 4096;

/// Unified I/O error for the agent transport.
///
/// This is a local error type that implements `embedded_io::Error` directly, so
/// the transport no longer depends on the `std` feature of `embedded-io` (which
/// provides `impl embedded_io::Error for std::io::Error`). Keeping that feature
/// off avoids modifying the gnrt-generated, "Do not edit!" `BUILD.gn` of
/// `embedded-io-0.6.1`, which would otherwise globally enable `std` for every
/// consumer of that crate.
#[derive(Debug)]
pub enum AgentError {
    /// Raw TCP / std I/O failure on the underlying `TcpStream`.
    Io(std::io::Error),
    /// TLS-layer failure reported by `embedded-tls`.
    Tls(TlsError),
}

impl fmt::Display for AgentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AgentError::Io(e) => write!(f, "{e}"),
            AgentError::Tls(e) => write!(f, "{e:?}"),
        }
    }
}

impl std::error::Error for AgentError {}

impl embedded_io::Error for AgentError {
    fn kind(&self) -> ErrorKind {
        match self {
            AgentError::Io(e) => match e.kind() {
                std::io::ErrorKind::NotFound => ErrorKind::NotFound,
                std::io::ErrorKind::PermissionDenied => ErrorKind::PermissionDenied,
                std::io::ErrorKind::ConnectionRefused => ErrorKind::ConnectionRefused,
                std::io::ErrorKind::ConnectionReset => ErrorKind::ConnectionReset,
                std::io::ErrorKind::ConnectionAborted => ErrorKind::ConnectionAborted,
                std::io::ErrorKind::NotConnected => ErrorKind::NotConnected,
                std::io::ErrorKind::AddrInUse => ErrorKind::AddrInUse,
                std::io::ErrorKind::AddrNotAvailable => ErrorKind::AddrNotAvailable,
                std::io::ErrorKind::BrokenPipe => ErrorKind::BrokenPipe,
                std::io::ErrorKind::AlreadyExists => ErrorKind::AlreadyExists,
                std::io::ErrorKind::InvalidInput => ErrorKind::InvalidInput,
                std::io::ErrorKind::InvalidData => ErrorKind::InvalidData,
                std::io::ErrorKind::TimedOut => ErrorKind::TimedOut,
                std::io::ErrorKind::Interrupted => ErrorKind::Interrupted,
                std::io::ErrorKind::UnexpectedEof => ErrorKind::Other,
                std::io::ErrorKind::Unsupported => ErrorKind::Unsupported,
                std::io::ErrorKind::OutOfMemory => ErrorKind::OutOfMemory,
                std::io::ErrorKind::WriteZero => ErrorKind::WriteZero,
                _ => ErrorKind::Other,
            },
            AgentError::Tls(e) => e.kind(),
        }
    }
}

impl From<std::io::Error> for AgentError {
    fn from(e: std::io::Error) -> Self {
        AgentError::Io(e)
    }
}

impl From<TlsError> for AgentError {
    fn from(e: TlsError) -> Self {
        AgentError::Tls(e)
    }
}

/// Adapter wrapping a `std::io` type as an `embedded_io` type.
///
/// This is a local replacement for `embedded_io_adapters::std::FromStd`, so that
/// the crate no longer depends on `embedded_io_adapters::std`. Unlike the
/// upstream adapter it surfaces errors as [`AgentError`] rather than
/// `std::io::Error`, which keeps the transport off the `embedded-io` `std`
/// feature.
#[derive(Clone)]
pub(crate) struct FromStd<T: ?Sized> {
    inner: T,
}

impl<T> FromStd<T> {
    fn new(inner: T) -> Self {
        Self { inner }
    }
}

impl<T: ?Sized> ErrorType for FromStd<T> {
    type Error = AgentError;
}

impl<T: std::io::Read + ?Sized> Read for FromStd<T> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        self.inner.read(buf).map_err(AgentError::from)
    }
}

impl<T: std::io::Write + ?Sized> Write for FromStd<T> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        match self.inner.write(buf) {
            Ok(0) if !buf.is_empty() => Err(AgentError::from(std::io::Error::from(
                std::io::ErrorKind::WriteZero,
            ))),
            Ok(n) => Ok(n),
            Err(e) => Err(AgentError::from(e)),
        }
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        self.inner.flush().map_err(AgentError::from)
    }
}

struct SimpleRng(fastrand::Rng);

impl RngCore for SimpleRng {
    fn next_u32(&mut self) -> u32 {
        self.0.u32(..)
    }

    fn next_u64(&mut self) -> u64 {
        self.0.u64(..)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill(dest);
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.0.fill(dest);
        Ok(())
    }
}

impl CryptoRng for SimpleRng {}

pub struct TlsSocketStd<'a> {
    inner: TlsConnection<'a, FromStd<TcpStream>, Aes128GcmSha256>,
}

impl<'a> ErrorType for TlsSocketStd<'a> {
    type Error = AgentError;
}

impl<'a> Read for TlsSocketStd<'a> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        self.inner.read(buf).map_err(AgentError::from)
    }
}

impl<'a> Write for TlsSocketStd<'a> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        self.inner.write(buf).map_err(AgentError::from)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        self.inner.flush().map_err(AgentError::from)
    }
}

pub enum AgentSocket<'a> {
    Plain(FromStd<TcpStream>),
    Tls(TlsSocketStd<'a>),
}

impl<'a> ErrorType for AgentSocket<'a> {
    type Error = AgentError;
}

impl<'a> Read for AgentSocket<'a> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        match self {
            Self::Plain(s) => s.read(buf),
            Self::Tls(s) => s.read(buf),
        }
    }
}

impl<'a> Write for AgentSocket<'a> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        match self {
            Self::Plain(s) => s.write(buf),
            Self::Tls(s) => s.write(buf),
        }
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        match self {
            Self::Plain(s) => s.flush(),
            Self::Tls(s) => s.flush(),
        }
    }
}

pub struct EmbeddedTlsTransport {
    read_buf: Vec<u8>,
    write_buf: Vec<u8>,
    rng: SimpleRng,
    sni: Option<String>,
}

impl EmbeddedTlsTransport {
    pub fn new() -> Self {
        Self {
            read_buf: vec![0u8; TLS_READ_RECORD_BUF_SIZE],
            write_buf: vec![0u8; TLS_WRITE_RECORD_BUF_SIZE],
            rng: SimpleRng(fastrand::Rng::with_seed(0xDEAD_BEEF_CAFE_BABE)),
            sni: None,
        }
    }

    pub fn with_sni(mut self, name: impl Into<String>) -> Self {
        self.sni = Some(name.into());
        self
    }
}

impl Default for EmbeddedTlsTransport {
    fn default() -> Self {
        Self::new()
    }
}

impl crate::http::SocketTransport for EmbeddedTlsTransport {
    type Error = AgentError;
    type Socket<'a> = AgentSocket<'a>;

    fn connect<'a>(
        &'a mut self,
        host: &str,
        port: u16,
        scheme: crate::http::Scheme,
    ) -> Result<Self::Socket<'a>, Self::Error> {
        println!("[http] connecting to {}:{}...", host, port);
        // let stream = TcpStream::connect(("124.72.129.70", port))?;
        let stream = TcpStream::connect((host, port))?;
        stream.set_nodelay(true)?;
        println!("[http] TCP connected");

        match scheme {
            crate::http::Scheme::Http => Ok(AgentSocket::Plain(FromStd::new(stream))),
            crate::http::Scheme::Https => {
                let server_name = self.sni.as_deref().unwrap_or(host);
                let write_buf_ptr = self.write_buf.as_ptr();
                let read_buf_ptr = self.read_buf.as_ptr();
                let mut tls: TlsConnection<FromStd<TcpStream>, Aes128GcmSha256> =
                    TlsConnection::new(
                        FromStd::new(stream),
                        &mut self.read_buf[..],
                        &mut self.write_buf[..],
                    );

                let config = TlsConfig::new()
                    .with_server_name(server_name)
                    .enable_rsa_signatures();
                println!("[http] TLS handshake...");
                let result =
                    tls.open::<SimpleRng, NoVerify>(TlsContext::new(&config, &mut self.rng));
                if let Err(ref e) = result {
                    println!("[http] TLS handshake failed: {:?}", e);
                    let wbuf = unsafe { core::slice::from_raw_parts(write_buf_ptr, 200) };
                    let rbuf = unsafe { core::slice::from_raw_parts(read_buf_ptr, 64) };
                    println!("[tls] ClientHello (write_buf first 200 bytes):");
                    for byte in wbuf {
                        print!("{byte:02x}");
                    }
                    println!();
                    println!("[tls] server response (read_buf first 64 bytes):");
                    for byte in rbuf {
                        print!("{byte:02x}");
                    }
                    println!();
                }
                result.map_err(AgentError::from)?;
                println!("[http] TLS established");

                Ok(AgentSocket::Tls(TlsSocketStd { inner: tls }))
            }
        }
    }
}
