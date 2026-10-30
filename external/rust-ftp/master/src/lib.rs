#![crate_name = "ftp"]
#![crate_type = "lib"]

//! ftp is an FTP client written in Rust.
//!
//! ### Usage
//!
//! Here is a basic usage example:
//!
//! ```rust
//! use ftp::FtpStream;
//! let mut ftp_stream = FtpStream::connect("127.0.0.1:21").unwrap_or_else(|err|
//!     panic!("{}", err)
//! );
//! let _ = ftp_stream.quit();
//! ```
//!
//! ### FTPS
//!
//! The client supports FTPS on demand. To enable it the client should be
//! compiled with feature `secure`. This crate supports two implementation of FTPS, one with [openssl](
//! https://crates.io/crates/openssl) and one with [native-tls](https://crates.io/crates/native-tls). By default it uses
//! [openssl](https://crates.io/crates/openssl) and you can switch to [native-tls](https://crates.io/crates/native-tls)
//! with features `secure` and `native-tls`
//!
//! The client uses explicit mode for connecting FTPS what means you should
//! connect the server as usually and then switch to the secure mode (TLS is used).
//! For better security it's the good practice to switch to the secure mode
//! before authentication.
//!
#![cfg_attr(
    all(feature = "secure", not(feature = "native-tls")),
    doc = r##"
## FTPS Usage

```rust,no_run
use ftp::FtpStream;
use ftp::openssl::ssl::{ SslContext, SslMethod };

let ftp_stream = FtpStream::connect("127.0.0.1:21").unwrap();
let ctx = SslContext::builder(SslMethod::tls()).unwrap().build();
// Switch to the secure mode
let mut ftp_stream = ftp_stream.into_secure(ctx).unwrap();
ftp_stream.login("anonymous", "anonymous").unwrap();
// Do other secret stuff
// Switch back to the insecure mode (if required)
let mut ftp_stream = ftp_stream.into_insecure().unwrap();
// Do all public stuff
let _ = ftp_stream.quit();
```
"##
)]
#![cfg_attr(
    all(feature = "secure", feature = "native-tls"),
    doc = r##"
## FTPS Usage

```rust,no_run
use ftp::FtpStream;
use ftp::native_tls::{TlsConnector, TlsStream};

let (ftp_stream, _welcome_msg) = FtpStream::connect("127.0.0.1:21").unwrap();
let mut ctx = TlsConnector::new().unwrap();
// Switch to the secure mode
let mut ftp_stream = ftp_stream.into_secure(ctx, "localhost").unwrap();
ftp_stream.login("anonymous", "anonymous").unwrap();
// Do other secret stuff
// Switch back to the insecure mode (if required)
let mut ftp_stream = ftp_stream.into_insecure().unwrap();
// Do all public stuff
let _ = ftp_stream.quit();
```
"##
)]
#[cfg(not(target_os = "blueos"))]
#[macro_use]
extern crate lazy_static;
#[cfg(not(target_os = "blueos"))]
extern crate chrono;
#[cfg(not(target_os = "blueos"))]
extern crate regex;

#[cfg(all(feature = "secure", feature = "native-tls"))]
pub extern crate native_tls;
#[cfg(all(feature = "secure", not(feature = "native-tls")))]
pub extern crate openssl;

mod data_stream;
mod ftp;
pub mod status;
pub mod types;

pub use self::ftp::FtpStream;
pub use self::types::FtpError;

/// A shorthand for a Result whose error type is always an FtpError.
pub type Result<T> = std::result::Result<T, FtpError>;
