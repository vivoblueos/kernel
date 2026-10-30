# rust-ftp

FTP client for Rust

[![Number of Crate Downloads](https://img.shields.io/crates/d/ftp.svg)](https://crates.io/crates/ftp)
[![Crate Version](https://img.shields.io/crates/v/ftp.svg)](https://crates.io/crates/ftp)
[![Crate License](https://img.shields.io/crates/l/ftp.svg)](https://crates.io/crates/ftp)
[![Build Status](https://github.com/mattnenterprise/rust-ftp/actions/workflows/ci.yml/badge.svg)](https://github.com/mattnenterprise/rust-ftp/actions)
[![Coverage Status](https://codecov.io/gh/mattnenterprise/rust-ftp/branch/master/graph/badge.svg?token=tQUj3RyZxI)](https://codecov.io/gh/mattnenterprise/rust-ftp)

[Documentation](https://docs.rs/ftp/)

---

- [rust-ftp](#rust-ftp)
  - [Installation](#installation)
  - [Usage](#usage)
  - [License](#license)
    - [Contribution](#contribution)
  - [Development environment](#development-environment)

## Installation

FTPS support is achieved through [rust-native-tls](https://github.com/sfackler/rust-native-tls) and is disabled by default. To enable it `secure` should be activated in `Cargo.toml`.

```toml
[dependencies]
ftp = { version = "<version>", features = ["secure"] }
```

## Usage

```rust
extern crate ftp;

use std::str;
use std::io::Cursor;
use ftp::FtpStream;

fn main() {
    // Create a connection to an FTP server and authenticate to it.
    let mut ftp_stream = FtpStream::connect("127.0.0.1:21").unwrap();
    let _ = ftp_stream.login("username", "password").unwrap();

    // Get the current directory that the client will be reading from and writing to.
    println!("Current directory: {}", ftp_stream.pwd().unwrap());

    // Change into a new directory, relative to the one we are currently in.
    let _ = ftp_stream.cwd("test_data").unwrap();

    // Retrieve (GET) a file from the FTP server in the current working directory.
    let remote_file = ftp_stream.simple_retr("ftpext-charter.txt").unwrap();
    println!("Read file with contents\n{}\n", str::from_utf8(&remote_file.into_inner()).unwrap());

    // Store (PUT) a file from the client to the current working directory of the server.
    let mut reader = Cursor::new("Hello from the Rust \"ftp\" crate!".as_bytes());
    let _ = ftp_stream.put("greeting.txt", &mut reader);
    println!("Successfully wrote greeting.txt");

    // Terminate the connection to the server.
    let _ = ftp_stream.quit();
}

```

## License

Licensed under either of

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.

## Development environment

All you need to develop rust-ftp and run the tests is Rust and Docker.
The `tests` folder contains a `Dockerfile` that installs and configures
the vsftpd server.

To create the Docker image:

```bash
docker build -t ftp-server tests
```

To start the FTP server that is tested against:

```bash
tests/ftp-server.sh
```

This script runs the `ftp-server` image in detached mode and starts the `vsftpd` daemon. It binds ports 21 (FTP) as well as the range 65000-65010 for passive connections.

Once you have an instance running, to run tests type:

```bash
cargo test --features secure
```

The following commands can be useful:

```bash
# List running containers of ftp-server image
# (to include stopped containers use -a option)
docker ps --filter ancestor=ftp-server

# To stop and remove a container
docker stop container_name
docker rm container_name

# To remove the image
docker rmi ftp-server
```
