# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

## [v0.2.2] - 2023-10-20

### Changed

- Added `#[repr(transparent)]` to `RO`, `RW`, and `WO` to ensure ABI
  compatibility with underlying register.

## [v0.2.1] - 2021-08-14

### Added

- Added more docs.rs targets

- The `modify` and `write` operations now take `&self`.

- [breaking-change] `RO` and `RW` no longer implement `Sync`. This is required
  to make the new `modify` and `write` sound.

- [breaking-change] `RO`, `RW` and `WO` now require that the inner value be
  `Copy`-able.

- docs: remove "guarantee" about some operations being atomic as this crate may
  be used in architectures different than the ARM Cortex-M.

## [v0.1.2] - 2016-10-15

### Added

- a (read-)`modify`(-write) method to `RW`

## [v0.1.1] - 2016-09-27

### Added

- Documentation link to Cargo metadata.

## v0.1.0 - 2016-09-27

### Added

- Read-Only (`RO`), Read-Write (`RW`) and Write-Only (`WO`) registers

[Unreleased]: https://github.com/rust-embedded/volatile-register/compare/v0.2.2...HEAD
[v0.2.2]: https://github.com/rust-embedded/volatile-register/compare/v0.2.1...v0.2.2
[v0.2.1]: https://github.com/rust-embedded/volatile-register/compare/v0.2.0...v0.2.1
[v0.2.0]: https://github.com/rust-embedded/volatile-register/compare/v0.1.2...v0.2.0
[v0.1.2]: https://github.com/rust-embedded/volatile-register/compare/v0.1.1...v0.1.2
[v0.1.1]: https://github.com/rust-embedded/volatile-register/compare/v0.1.0...v0.1.1
