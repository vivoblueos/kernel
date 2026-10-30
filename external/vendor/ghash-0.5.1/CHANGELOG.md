# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## 0.5.1 (2024-03-03)
### Added
- add `new_with_init_block` ([#195])

[#195]: https://github.com/RustCrypto/universal-hashes/pull/195

## 0.5.0 (2022-07-31)
### Changed
- Relax `zeroize` constraints ([#147])
- Upgrade to Rust 2021 edition ([#147])
- Bump `polyval` to v0.6.0 ([#164])

[#147]: https://github.com/RustCrypto/universal-hashes/pull/147
[#164]: https://github.com/RustCrypto/universal-hashes/pull/164

## 0.4.4 (2021-08-27)
### Changed
- Relax `zeroize` constraints ([#141])

[#141]: https://github.com/RustCrypto/universal-hashes/pull/141

## 0.4.3 (2021-07-20)
### Changed
- Pin `zeroize` dependency to v1.3 ([#134])

[#134]: https://github.com/RustCrypto/universal-hashes/pull/134

## 0.4.2 (2021-05-31)
### Added
- Nightly-only ARMv8 intrinsics support gated under the `armv8` feature ([#126])

[#126]: https://github.com/RustCrypto/universal-hashes/pull/126

## 0.4.1 (2021-05-05)
### Added
- `force-soft` feature ([#121])

[#121]: https://github.com/RustCrypto/universal-hashes/pull/121

## 0.4.0 (2021-04-29)
### Changed
- Bump `polyval` crate dependency to v0.5; MSRV 1.49+ ([#114], [#119])

[#114]: https://github.com/RustCrypto/universal-hashes/pull/114
[#119]: https://github.com/RustCrypto/universal-hashes/pull/119

## 0.3.1 (2020-12-26)
### Added
- `Debug` impl using `opaque-debug` ([#105])

### Changed
- Use `polyval::mulx` ([#109])

[#105]: https://github.com/RustCrypto/universal-hashes/pull/105
[#109]: https://github.com/RustCrypto/universal-hashes/pull/109

## 0.3.0 (2020-06-06)
### Changed
- Bump `polyval` dependency to v0.4 ([#59])
- Bump `universal-hash` dependency to v0.4; MSRV 1.41 ([#52], [#57])
- Rename `result` methods to to `finalize` ([#56])

[#59]: https://github.com/RustCrypto/universal-hashes/pull/59
[#57]: https://github.com/RustCrypto/universal-hashes/pull/57
[#56]: https://github.com/RustCrypto/universal-hashes/pull/56
[#52]: https://github.com/RustCrypto/universal-hashes/pull/52

## 0.2.3 (2019-11-14)
### Changed
- Upgrade to `zeroize` 1.0 ([#33])

[#33]: https://github.com/RustCrypto/universal-hashes/pull/33

## 0.2.2 (2019-10-06)
### Fixed
- Revert mulX_POLYVAL changes from [#28] ([#31])

[#31]: https://github.com/RustCrypto/universal-hashes/pull/31

## 0.2.1 (2019-10-05)
### Changed
- Upgrade to `polyval` v0.3 ([#28], [#29])

[#29]: https://github.com/RustCrypto/universal-hashes/pull/29
[#28]: https://github.com/RustCrypto/universal-hashes/pull/28

## 0.2.0 (2019-10-04)
### Changed
- Upgrade to `polyval` v0.2 and `universal-hash` crate v0.3 ([#22])

[#22]: https://github.com/RustCrypto/universal-hashes/pull/22

## 0.1.0 (2019-09-19)

- Initial release
