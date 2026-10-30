#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![allow(dead_code)]
#![cfg_attr(
    feature = "async",
    allow(stable_features, incomplete_features, unknown_lints, async_fn_in_trait)
)]
#![cfg_attr(feature = "async", feature(impl_trait_projections, async_fn_in_trait))]

//! Embedded-TLS is a Rust-native TLS 1.3 implementation that works in a no-std environment. The
//! implementation is work in progress, but the [example clients](https://github.com/drogue-iot/embedded-tls/tree/main/examples) should work against the [rustls](https://github.com/ctz/rustls) echo server.
//!
//! The client supports both async and blocking modes. By default, the `async` and `std` features are enabled. The `async` feature requires Rust nightly, while the blocking feature works on Rust stable.
//!
//! To use the async mode, import `embedded_tls::*`. To use the blocking mode, import `embedded_tls::blocking::*`.
//!
//! Some features like certificate validation are still not implemented, have a look at [open issues](https://github.com/drogue-iot/embedded-tls/issues).
//! Only supports writing/receiving one frame at a time, hence using a frame buffer larger than 16k is not currently needed.  You may use a lower frame buffer size, but there is no guarantee that it will be able to parse any TLS 1.3 frame.
//!
//! Usage of this crate should fit in 20 kB of RAM assuming a frame buffer of 16 kB (max TLS record size). This is not including the space used to hold the CA and any client certificates.
//!
//! Some memory usage statistics for async operation:
//!
//! * TlsConnection: frame_buffer size + 2kB for the rest. This can probably be reduced with some additional tuning.
//! * Handshake stack usage: currently at 2 kB
//! * Write stack usage: currently at 560 B
//! * Read stack usage: currently at 232 B
//!
//!
//! NOTE: This is very fresh and is probably not meeting all parts of the TLS 1.3 spec. If you find anything you'd like to get implemented, feel free to raise an issue.

/*!
# Example

```
use embedded_tls::*;
use embedded_io_adapters::tokio_1::FromTokio;
use rand::rngs::OsRng;
use tokio::net::TcpStream;

#[tokio::main]
async fn main() {
    let stream = TcpStream::connect("http.sandbox.drogue.cloud:443").await.expect("error creating TCP connection");

    println!("TCP connection opened");
    let mut read_record_buffer = [0; 16384];
    let mut write_record_buffer = [0; 16384];
    let config = TlsConfig::new()
        .with_server_name("http.sandbox.drogue.cloud");
    let mut tls: TlsConnection<FromTokio<TcpStream>, Aes128GcmSha256> =
        TlsConnection::new(FromTokio::new(stream), &mut read_record_buffer, &mut write_record_buffer);

    // Allows disabling cert verification, in case you are using PSK and don't need it, or are just testing.
    // otherwise, use embedded_tls::webpki::CertVerifier, which only works on std for now.
    tls.open::<OsRng, NoVerify>(TlsContext::new(&config, &mut OsRng)).await.expect("error establishing TLS connection");

    println!("TLS session opened");
}
```
*/

// This mod MUST go first, so that the others see its macros.
pub(crate) mod fmt;

use parse_buffer::ParseError;
pub mod alert;
mod application_data;
pub mod blocking;
mod buffer;
mod change_cipher_spec;
mod cipher_suites;
mod common;
mod config;
mod connection;
mod content_types;
mod crypto_engine;
mod extensions;
mod handshake;
mod key_schedule;
mod parse_buffer;
pub mod read_buffer;
mod record;
mod record_reader;
mod split;
mod write_buffer;

#[cfg(feature = "webpki")]
pub mod webpki;

#[cfg(feature = "async")]
mod asynch;

#[cfg(feature = "async")]
pub use asynch::*;

#[derive(Debug, Copy, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum TlsError {
    ConnectionClosed,
    Unimplemented,
    MissingHandshake,
    HandshakeAborted(alert::AlertLevel, alert::AlertDescription),
    AbortHandshake(alert::AlertLevel, alert::AlertDescription),
    IoError,
    InternalError,
    InvalidRecord,
    UnknownContentType,
    InvalidNonceLength,
    InvalidTicketLength,
    UnknownExtensionType,
    InsufficientSpace,
    InvalidHandshake,
    InvalidCipherSuite,
    InvalidSignatureScheme,
    InvalidSignature,
    InvalidExtensionsLength,
    InvalidSessionIdLength,
    InvalidSupportedVersions,
    InvalidApplicationData,
    InvalidKeyShare,
    InvalidCertificate,
    InvalidCertificateEntry,
    InvalidCertificateRequest,
    UnableToInitializeCryptoEngine,
    ParseError(ParseError),
    OutOfMemory,
    CryptoError,
    EncodeError,
    DecodeError,
    Io(embedded_io::ErrorKind),
}

impl embedded_io::Error for TlsError {
    fn kind(&self) -> embedded_io::ErrorKind {
        match self {
            Self::Io(k) => *k,
            _ => {
                error!("TLS error: {:?}", self);
                embedded_io::ErrorKind::Other
            }
        }
    }
}

#[cfg(feature = "std")]
mod stdlib {
    use crate::config::TlsClock;

    use std::time::SystemTime;
    impl TlsClock for SystemTime {
        fn now() -> Option<u64> {
            Some(
                SystemTime::now()
                    .duration_since(SystemTime::UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
            )
        }
    }
}

#[cfg(feature = "std")]
pub use stdlib::*;
