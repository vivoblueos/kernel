# [RustCrypto]: Prime Order Elliptic Curve Formulas

[![crate][crate-image]][crate-link]
[![Docs][docs-image]][docs-link]
[![Build Status][build-image]][build-link]
![Apache2/MIT licensed][license-image]
![Rust Version][rustc-image]
[![Project Chat][chat-image]][chat-link]

Pure Rust implementation of complete addition formulas for prime order elliptic
curves ([Renes-Costello-Batina 2015]). Generic over field elements and curve
equation coefficients.

[Documentation][docs-link]

## About

This crate provides a generic implementation of complete formulas for prime
order elliptic curves which are defined by the short [Weierstrass equation]:

```text
y² = x³ + ax + b
```

It's used to implement the following elliptic curves:

- [`p192`]: NIST P-192
- [`p224`]: NIST P-224
- [`p256`]: NIST P-256
- [`p384`]: NIST P-384
- [`p521`]: NIST P-521
- [`sm2`]: ShangMi 2

## ⚠️ Security Warning

The elliptic curve arithmetic contained in this crate has never been
independently audited!

This crate has been designed with the goal of ensuring that secret-dependent
operations are performed in constant time (using the `subtle` crate and
constant-time formulas). However, it has not been thoroughly assessed to ensure
that generated assembly is constant time on common CPU architectures.

USE AT YOUR OWN RISK!

## Minimum Supported Rust Version

Rust **1.65** or higher.

Minimum supported Rust version can be changed in the future, but it will be
done with a minor version bump.

## SemVer Policy

- All on-by-default features of this library are covered by SemVer
- MSRV is considered exempt from SemVer as noted above

## License

All crates licensed under either of:

- [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0)
- [MIT license](http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[//]: # (badges)

[crate-image]: https://buildstats.info/crate/primeorder
[crate-link]: https://crates.io/crates/primeorder
[docs-image]: https://docs.rs/primeorder/badge.svg
[docs-link]: https://docs.rs/primeorder/
[build-image]: https://github.com/RustCrypto/elliptic-curves/actions/workflows/primeorder.yml/badge.svg
[build-link]: https://github.com/RustCrypto/elliptic-curves/actions/workflows/primeorder.yml
[license-image]: https://img.shields.io/badge/license-Apache2.0/MIT-blue.svg
[rustc-image]: https://img.shields.io/badge/rustc-1.65+-blue.svg
[chat-image]: https://img.shields.io/badge/zulip-join_chat-blue.svg
[chat-link]: https://rustcrypto.zulipchat.com/#narrow/stream/260040-elliptic-curves

[//]: # (links)

[RustCrypto]: https://github.com/rustcrypto/
[Renes-Costello-Batina 2015]: https://eprint.iacr.org/2015/1060
[Weierstrass equation]: https://crypto.stanford.edu/pbc/notes/elliptic/weier.html
[`p192`]: https://github.com/RustCrypto/elliptic-curves/tree/master/p192
[`p224`]: https://github.com/RustCrypto/elliptic-curves/tree/master/p224
[`p256`]: https://github.com/RustCrypto/elliptic-curves/tree/master/p256
[`p384`]: https://github.com/RustCrypto/elliptic-curves/tree/master/p384
[`p521`]: https://github.com/RustCrypto/elliptic-curves/tree/master/p384
[`sm2`]: https://github.com/RustCrypto/elliptic-curves/tree/master/sm2
