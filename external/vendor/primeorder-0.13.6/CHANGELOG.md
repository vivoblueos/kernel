# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## 0.13.6 (2023-11-15)
### Removed
-  `Invert` bounds on `FieldElement` ([#985])

[#985]: https://github.com/RustCrypto/elliptic-curves/pull/985

## 0.13.5 (2023-11-15) [YANKED]
### Added
- `alloc` feature ([#982])

[#982]: https://github.com/RustCrypto/elliptic-curves/pull/982

## 0.13.4 (2023-11-15) [YANKED]
### Added
- `BatchInvert` and `BatchNormalize` impls ([#971])

### Changed
- Bump `elliptic-curve` to v0.13.7 ([#979])

[#971]: https://github.com/RustCrypto/elliptic-curves/pull/971
[#979]: https://github.com/RustCrypto/elliptic-curves/pull/979

## 0.13.3 (2023-11-02)
### Added
- Inline annotations on `conditional_select` ([#942])

### Changed
- Support field elements larger than 64-bytes in `impl_projective_arithmetic_tests!` ([#951])

[#942]: https://github.com/RustCrypto/elliptic-curves/pull/942
[#951]: https://github.com/RustCrypto/elliptic-curves/pull/951

## 0.13.2 (2023-05-29)
### Changed
- Improve decoding performance for uncompressed SEC1 points ([#891])

[#891]: https://github.com/RustCrypto/elliptic-curves/pull/891

## 0.13.1 (2023-04-09)
### Added
- `impl_bernstein_yang_invert!` macro ([#786])
- `impl_field_invert_tests!` macro ([#786])
- `impl_field_identity_tests!` macro ([#790])
- `impl_field_sqrt_tests!` macro ([#790], [#800])

### Fixed
- Correct product definition for empty iterators ([#802])

[#786]: https://github.com/RustCrypto/elliptic-curves/pull/786
[#790]: https://github.com/RustCrypto/elliptic-curves/pull/790
[#800]: https://github.com/RustCrypto/elliptic-curves/pull/800
[#802]: https://github.com/RustCrypto/elliptic-curves/pull/802

## 0.13.0 (2023-03-03)
### Added
- Support curves with any `a`-coefficient ([#728], [#729])
- `impl_primefield_tests!` macro ([#739])

### Changed
- Use `AffineCoordinates` trait ([#734])
- Rename `impl_field_element!` to `impl_mont_field_element!` ([#762])
- Bump `elliptic-curve` dependency to v0.13 ([#770])
- Bump `ecdsa` to v0.16 ([#770])

[#728]: https://github.com/RustCrypto/elliptic-curves/pull/728
[#729]: https://github.com/RustCrypto/elliptic-curves/pull/729
[#734]: https://github.com/RustCrypto/elliptic-curves/pull/734
[#739]: https://github.com/RustCrypto/elliptic-curves/pull/739
[#762]: https://github.com/RustCrypto/elliptic-curves/pull/762
[#770]: https://github.com/RustCrypto/elliptic-curves/pull/770

## 0.12.1 (2023-01-22)
### Added
- Impl `From/ToEncodedPoint` for `ProjectivePoint` ([#722])

[#722]: https://github.com/RustCrypto/elliptic-curves/pull/722

## 0.12.0 (2023-01-16)

Initial stable release.

NOTE: other versions skipped to synchronize version numbers with
`elliptic-curve`, `k256`, `p256`, and `p384`.

## 0.0.2 (2022-12-29)

## 0.0.1 (2022-11-06)
