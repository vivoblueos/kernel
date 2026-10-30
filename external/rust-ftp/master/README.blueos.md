# rust-ftp (BlueOS Port)

This repository is a **BlueOS-adapted** version of [rust-ftp](https://github.com/mattnenterprise/rust-ftp), provided as a simple FTP crate for the BlueOS environment.

**Based on commit:** 35b2006556dbf33eed2a73843987205b648ce2e2

## 1. License and Copyright Notice

This project is a BlueOS-adapted version of [rust-ftp](https://github.com/mattnenterprise/rust-ftp),  
which is dual-licensed under the Apache License 2.0 and the MIT License.  

This BlueOS port is **licensed exclusively under the Apache License, Version 2.0**.  

You may obtain a copy of the Apache 2.0 license at:  
<https://www.apache.org/licenses/LICENSE-2.0>  

The original rust-ftp project's copyright and license notices are preserved in the `LICENSE-APACHE` and `LICENSE-MIT` files included in this repository.  

No NOTICE file is provided as the original rust-ftp project does not include one.  

By using this software, you agree to comply with the terms of the Apache License 2.0 applicable to this BlueOS adaptation.

## 2. BlueOS-Specific Modifications

The original **rust-ftp** project has been modified to enable compilation and execution on BlueOS:

### Build Integration
- Added a `BUILD.gn` script for integration with the BlueOS GN build system.

### Standard Library Support
- Added `librs` and `rsrt` crates to provide Rust `std` support for BlueOS.
- Removed `chrono`, `regex`, and `lazy_static` crates (not yet included in BlueOS) and replaced their usage with standard library equivalents.

### Passive Mode (PASV) Parsing
- Updated `src/ftp.rs` to replace the `regex::Regex`-based PASV response parser with a manual implementation.

### MDTM and SIZE Commands
- The MDTM and SIZE commands are currently unsupported because they depend on `utc` and `regex`, which are not yet included in BlueOS.

---

## 3. Usage Example

See [apps_example/ftp_client](https://github.com/vivoblueos/apps_example/tree/main/ftp_client) for a practical usage example.

---

## 4. Notes
- This sample has only been tested in the BlueOS environment.
- The build must use the Rust toolchain provided by BlueOS.
- Ensure that the FTP server supports **passive mode** (PASV).
