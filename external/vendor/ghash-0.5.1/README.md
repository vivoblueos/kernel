# RustCrypto: GHASH

[![crate][crate-image]][crate-link]
[![Docs][docs-image]][docs-link]
![Apache2/MIT licensed][license-image]
![Rust Version][rustc-image]
[![Build Status][build-image]][build-link]
[![HAZMAT][hazmat-image]][hazmat-link]

[GHASH][1] is a [universal hash function][2] which operates over GF(2^128) and
can be used for constructing a [Message Authentication Code (MAC)][3].

Its primary intended use is for implementing [AES-GCM][4].

[Documentation][docs-link]

## Security

### ⚠️ Warning: [Hazmat!][hazmat-link]

Universal hash functions have subtle security properties and using them
correctly is difficult. See the [toplevel README.md](../README.md) for more
information.

USE AT YOUR OWN RISK!

### Notes

This crate has received one [security audit by NCC Group][5], with no significant
findings. We would like to thank [MobileCoin][6] for funding the audit.

All implementations contained in the crate are designed to execute in constant
time, either by relying on hardware intrinsics (i.e. AVX2 on x86/x86_64), or
using a portable implementation which is only constant time on processors which
implement constant-time multiplication.

It is not suitable for use on processors with a variable-time multiplication
operation (e.g. short circuit on multiply-by-zero / multiply-by-one, such as
certain 32-bit PowerPC CPUs and some non-ARM microcontrollers).

## License

Licensed under either of:

 * [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0)
 * [MIT license](http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[//]: # (badges)

[crate-image]: https://img.shields.io/crates/v/ghash.svg
[crate-link]: https://crates.io/crates/ghash
[docs-image]: https://docs.rs/ghash/badge.svg
[docs-link]: https://docs.rs/ghash/
[license-image]: https://img.shields.io/badge/license-Apache2.0/MIT-blue.svg
[rustc-image]: https://img.shields.io/badge/rustc-1.56+-blue.svg
[build-image]: https://github.com/RustCrypto/universal-hashes/workflows/ghash/badge.svg?branch=master&event=push
[build-link]: https://github.com/RustCrypto/universal-hashes/actions?query=workflow%3Aghash
[hazmat-image]: https://img.shields.io/badge/crypto-hazmat%E2%9A%A0-red.svg
[hazmat-link]: https://github.com/RustCrypto/meta/blob/master/HAZMAT.md

[//]: # (footnotes)

[1]: https://en.wikipedia.org/wiki/Galois/Counter_Mode#Mathematical_basis
[2]: https://en.wikipedia.org/wiki/Universal_hashing
[3]: https://en.wikipedia.org/wiki/Message_authentication_code
[4]: https://en.wikipedia.org/wiki/Galois/Counter_Mode
[5]: https://research.nccgroup.com/2020/02/26/public-report-rustcrypto-aes-gcm-and-chacha20poly1305-implementation-review/
[6]: https://www.mobilecoin.com/
