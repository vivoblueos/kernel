# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.2.2] - 2026-02-07

### Changed

- Minor performance and code size optimization

### Added

- `GlobalTlsf` now implements `Default`.

### Fixed

- Addressed [illegal](https://doc.rust-lang.org/1.91.0/reference/behavior-considered-undefined.html#r-undefined.validity.reference-box) reference creation (e.g., borrowing a partially initialized object from a raw pointer) that triggered errors on Miri.
- Implemented a work-around for `GlobalAlloc::{dealloc,realloc}` receiving allocation pointers with insufficient provenance on Miri.

## [0.2.1] - 2023-02-17

### Fixed

- Bump `svgbobdoc` to `^0.3` to address a future-incompat report
  [rust-lang/rust#79813](https://github.com/rust-lang/rust/issues/79813)
- Don't enable the default features of
  [`const-default`](https://crates.io/crates/const-default/1.0.0) so that it
  can compile for targets with no atomics support

## [0.2.0] - 2022-08-31

### Changed

- **Breaking:** Raised the minimum supported Rust version to 1.61
- Documentation improvements
- Descriptive compile-time panic messages

### Added

- **Breaking:** `CAlloc::allocation_usable_size`
- `{Global,}Tlsf::new`
- `FlexTlsf::new` as a `const fn`
- `ConstDefault` implementation for `Tlsf`
- `Tlsf::iter_blocks` (unstable), which lets you iterate through memory blocks for diagnostic purposes.
- `{Flex,}Tlsf::allocation_usable_size` (unstable)

### Removed

- **Breaking:** `{Global,}Tlsf::INIT`
- **Breaking:** `Init` (superseded by `ConstDefault` from [`const-default`](https://crates.io/crates/const-default/1.0.0))

## [0.1.2] - 2021-05-30

- Performance and code size optimization
- **Added:** `GlobalTlsf` now provides a `malloc`-compatible interface.
- **Fixed:** Raised the version requirement of `libc` to 0.2.56, where `MAP_FIXED_NOREPLACE` was added.

## [0.1.1] - 2021-05-23

- **Added:** `GlobalTlsf` now supports POSIX-compliant systems (`cfg(unix)`).
- **Fixed:** Addressed a bug in `Tlsf::reallocate` that caused an incorrect amount of data to be copied (possibly corrupting memory or crashing the program) during a moving reallocation.

## 0.1.0 - 2021-05-21

- Initial release.

[Unreleased]: https://github.com/yvt/rlsf/compare/0.2.2...HEAD
[0.2.2]: https://github.com/yvt/rlsf/compare/0.2.1...0.2.2
[0.2.1]: https://github.com/yvt/rlsf/compare/0.2.0...0.2.1
[0.2.0]: https://github.com/yvt/rlsf/compare/0.1.2...0.2.0
[0.1.2]: https://github.com/yvt/rlsf/compare/0.1.1...0.1.2
[0.1.1]: https://github.com/yvt/rlsf/compare/0.1.0...0.1.1
