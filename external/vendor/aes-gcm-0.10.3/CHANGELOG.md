# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## 0.10.3 (2023-09-21)
### Security
- Avoid exposing plaintext on tag verification failure ([#551])

[#551]: https://github.com/RustCrypto/AEADs/pull/551

## 0.10.2 (2023-05-20)
### Added
- `rand_core` feature to all crates ([#467])
- Support for partial tag sizes ([#501])
- `ArrayVec` support ([#503])

[#467]: https://github.com/RustCrypto/AEADs/pull/467
[#501]: https://github.com/RustCrypto/AEADs/pull/501
[#503]: https://github.com/RustCrypto/AEADs/pull/503

## 0.10.1 (2022-07-31)
### Fixed
- rustdoc typos and formatting ([#461], [#462])

[#461]: https://github.com/RustCrypto/AEADs/pull/461
[#462]: https://github.com/RustCrypto/AEADs/pull/462

## 0.10.0 (2022-07-31)
### Added
- `getrandom` feature ([#446])

### Changed
- Bump `aes` dependency to v0.8 ([#430])
- Rust 2021 edition upgrade; MSRV 1.56+ ([#435])
- Bump `aead` dependency to v0.5 ([#444])
- Bump `ghash` dependency to v0.5 ([#454])

[#435]: https://github.com/RustCrypto/AEADs/pull/435
[#444]: https://github.com/RustCrypto/AEADs/pull/444
[#446]: https://github.com/RustCrypto/AEADs/pull/446
[#454]: https://github.com/RustCrypto/AEADs/pull/454

## 0.9.4 (2021-08-28)
### Changed
- Relax `subtle` and `zeroize` requirements ([#360])

[#360]: https://github.com/RustCrypto/AEADs/pull/360

## 0.9.3 (2021-07-20)
### Changed
- Pin `zeroize` dependency to v1.3 and `subtle` to v2.4 ([#349])

[#349]: https://github.com/RustCrypto/AEADs/pull/349

## 0.9.2 (2021-05-31)
### Added
- Nightly-only `armv8` feature ([#318])

[#318]: https://github.com/RustCrypto/AEADs/pull/318

## 0.9.1 (2021-05-04)
### Added
- `force-soft` feature ([#305])

[#305]: https://github.com/RustCrypto/AEADs/pull/305

## 0.9.0 (2021-04-29)
### Added
- Wycheproof test vectors ([#274])

### Changed
- Bump `aead` crate dependency to v0.4 ([#270])
- Bump `aes` crate dependency to v0.7; MSRV 1.49+ ([#283])
- Bump `ctr` crate dependency to v0.7 ([#283])
- Bump `ghash` crate dependency to v0.4 ([#284])

[#270]: https://github.com/RustCrypto/AEADs/pull/270
[#274]: https://github.com/RustCrypto/AEADs/pull/274
[#283]: https://github.com/RustCrypto/AEADs/pull/283
[#284]: https://github.com/RustCrypto/AEADs/pull/284

## 0.8.0 (2020-10-16)
### Changed
- Replace `block-cipher`/`stream-cipher` with `cipher` crate ([#229])
- Bump `aes` dependency to v0.6 ([#229])
- Use `ctr::Ctr32BE` ([#227])

[#229]: https://github.com/RustCrypto/AEADs/pull/229
[#227]: https://github.com/RustCrypto/AEADs/pull/227

## 0.7.0 (2020-09-17)
### Added
- Optional `std` feature; disabled by default ([#217])

### Changed
- Renamed generic parameters to `Aes` and `NonceSize` ([#166])
- Upgrade `aes` to v0.5; `block-cipher` to v0.8 ([#209])

[#217]: https://github.com/RustCrypto/AEADs/pull/217
[#209]: https://github.com/RustCrypto/AEADs/pull/209
[#166]: https://github.com/RustCrypto/AEADs/pull/166

## 0.6.0 (2020-06-06)
### Changed
- Bump `aead` crate dependency to v0.3.0; MSRV 1.41+ ([#140])

[#140]: https://github.com/RustCrypto/AEADs/pull/140

## 0.5.0 (2020-03-15)
### Added
- Support for non-96-bit nonces ([#126])

### Changed
- `AesGcm` type is now generic around nonce size ([#126])

[#126]:  https://github.com/RustCrypto/AEADs/pull/126

## 0.4.2 (2020-03-09)
### Fixed
- Off-by-one error in `debug_assert` for `BlockCipher::ParBlocks` ([#104])

[#104]: https://github.com/RustCrypto/AEADs/pull/104

## 0.4.1 (2020-03-07) - YANKED, see [#104]
### Added
- Support instantiation from an existing cipher instance ([#101])

[#101]: https://github.com/RustCrypto/AEADs/pull/101

## 0.4.0 (2020-03-07) - YANKED, see [#104]
### Added
- `aes` cargo feature; 3rd-party AES crate support ([#96])

### Changed
- Make generic around `BlockCipher::ParBlocks` ([#97])

[#96]: https://github.com/RustCrypto/AEADs/pull/96
[#97]: https://github.com/RustCrypto/AEADs/pull/97

## 0.3.2 (2020-02-27)
### Fixed
- Wording in documentation about security audit ([#84])

[#84]: https://github.com/RustCrypto/AEADs/pull/84

## 0.3.1 (2020-02-26)
### Added
- Notes about NCC audit to documentation ([#80])

[#80]: https://github.com/RustCrypto/AEADs/pull/80

## 0.3.0 (2019-11-26)
### Added
- `heapless` feature ([#51])

[#51]: https://github.com/RustCrypto/AEADs/pull/51

## 0.2.1 (2019-11-26)
### Added
- Document in-place API ([#49])

[#49]: https://github.com/RustCrypto/AEADs/pull/49

## 0.2.0 (2019-11-26)
### Changed
- Upgrade `aead` crate to v0.2; `alloc` now optional ([#43])

[#43]: https://github.com/RustCrypto/AEADs/pull/43

## 0.1.1 (2019-11-14)
### Changed
- Upgrade `zeroize` to 1.0 ([#36])

[#36]: https://github.com/RustCrypto/AEADs/pull/36

## 0.1.0 (2019-10-06)
- Initial release
