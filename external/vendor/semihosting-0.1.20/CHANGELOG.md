# Changelog

All notable changes to this project will be documented in this file.

This project adheres to [Semantic Versioning](https://semver.org).

Releases may yanked if there is a security bug, a soundness bug, or a regression.

<!--
Note: In this file, do not use the hard wrap in the middle of a sentence for compatibility with GitHub comment style markdown rendering.
-->

## [Unreleased]

## [0.1.20] - 2025-03-19

- Add `io::ErrorKind::InvalidFilename` variant to reflect [upstream stabilization in Rust 1.87](https://github.com/rust-lang/rust/pull/134076). ([b6f25e3](https://github.com/taiki-e/semihosting/commit/b6f25e33031c6aa9c4198cf78157170f4030c7a6))

## [0.1.19] - 2025-02-19

- Change to open stdio handles (`io::Std{in,out,err}`) in "text" mode due to some tools doesn't support opening them in "binary" mode. ([#16](https://github.com/taiki-e/semihosting/issues/16))

  This doesn't change the open behavior on files such as `fs::File`.

- Implement `From<alloc::ffi::NulError>` and `From<alloc::collections::TryReserveError>` for `io::Error` when `alloc` feature is enabled to align `std::io::Error`.

- Implement `io::{Read,Write,Seek}` for `&mut impl io::{Read,Write,Seek}` and `alloc::boxed::Box<impl {Read,Write,Seek}>` (when `alloc` feature is enabled) to align `std::io`.

- Implement `io::Read` for `&[u8]` and `alloc::collections::VecDeque<u8>` (when `alloc` feature is enabled) to align `std::io`.

- Implement `io::Write` for `&mut [u8]`, `alloc::vec::Vec<u8>` (when `alloc` feature is enabled), and `alloc::collections::VecDeque<u8>` (when `alloc` feature is enabled) to align `std::io`.

## [0.1.18] - 2025-01-06

- Add `io::ErrorKind::CrossesDevices` variant to reflect [upstream stabilization in Rust 1.85](https://github.com/rust-lang/rust/pull/130209). ([0a09ce5](https://github.com/taiki-e/semihosting/commit/0a09ce540784739f972e76fe719a573a744b98eb))

- Add `io::ErrorKind::QuotaExceeded` variant to reflect [upstream stabilization in Rust 1.85](https://github.com/rust-lang/rust/pull/130254). ([36b069a](https://github.com/taiki-e/semihosting/commit/36b069ab0e56b25bb64b5d7390ece5ce41534c94))

## [0.1.17] - 2024-12-04

- Respect [`RUSTC_BOOTSTRAP=-1` recently added in nightly](https://github.com/rust-lang/rust/pull/132993) in rustc version detection.

- Documentation improvements.

## [0.1.16] - 2024-10-13

- Add more `io::ErrorKind` variants to reflect [upstream stabilization in Rust 1.83](https://github.com/rust-lang/rust/pull/128316). ([9677c7b](https://github.com/taiki-e/semihosting/commit/9677c7be05fee821113e9d36b34e8815532e6f5c))

- Improve compile error messages. ([80f1153](https://github.com/taiki-e/semihosting/commit/80f115310a28e44c2d48b3cc714fc1048aa67386))

## [0.1.15] - 2024-09-15

- Add `process::{ExitCode,Termination}`.

## [0.1.14] - 2024-08-23

- Add `#[must_use]` to `OwnedFd::into_raw_fd`.

## [0.1.13] - 2024-07-22

- Open files in "binary" mode to match `std::fs::File`'s behavior. ([#12](https://github.com/taiki-e/semihosting/issues/12))

## [0.1.12] - 2024-07-09

- Fix [build issue with `esp` toolchain](https://github.com/taiki-e/semihosting/issues/11).

## [0.1.11] - 2024-06-16

**Note:** This release has been yanked due to an issue fixed in 0.1.12.

- Implement `core::error::Error` for `semihosting::io::Error` at Rust 1.81+. ([8701460](https://github.com/taiki-e/semihosting/commit/8701460101e5c9838bb09062435590f834837861))

## [0.1.10] - 2024-05-06

- Make `impl<Fd: AsFd>` impl take `?Sized`. ([2c7b911](https://github.com/taiki-e/semihosting/commit/2c7b9112a42b14f27def67f3b6fd35258c6f2f2b))

## [0.1.9] - 2024-04-21

- Add `trap-hlt` feature to use `HLT` instruction on Arm A+R profile. See the [documentation](https://github.com/taiki-e/semihosting#optional-features-trap-hlt) for details.

## [0.1.8] - 2024-04-21

- Respect `RUSTC_WRAPPER` in rustc version detection.

- Documentation improvements.

## [0.1.7] - 2024-03-21

- Support Xtensa (OpenOCD Semihosting) under the `openocd-semihosting` feature. ([#9](https://github.com/taiki-e/semihosting/pull/9))

## [0.1.6] - 2024-03-02

- Documentation improvements.

## [0.1.5] - 2023-12-27

- Expose raw syscall interface as public API. ([#7](https://github.com/taiki-e/semihosting/pull/7), thanks @t-moe)

## [0.1.4] - 2023-08-25

- Update `unwinding` to 0.2.

## [0.1.3] - 2023-07-27

- Fix build error on MIPS32r6 and MIPS64r6 since [nightly-2023-07-19's target_arch change](https://github.com/rust-lang/rust/pull/112374).

## [0.1.2] - 2023-05-06

- Enable `portable-atomic`'s `require-cas` feature to display helpful error messages to users on targets requiring additional action on the user side to provide atomic CAS.

## [0.1.1] - 2023-04-09

- Improve panic message on stable.

## [0.1.0] - 2023-03-22

Initial release

[Unreleased]: https://github.com/taiki-e/semihosting/compare/v0.1.20...HEAD
[0.1.20]: https://github.com/taiki-e/semihosting/compare/v0.1.19...v0.1.20
[0.1.19]: https://github.com/taiki-e/semihosting/compare/v0.1.18...v0.1.19
[0.1.18]: https://github.com/taiki-e/semihosting/compare/v0.1.17...v0.1.18
[0.1.17]: https://github.com/taiki-e/semihosting/compare/v0.1.16...v0.1.17
[0.1.16]: https://github.com/taiki-e/semihosting/compare/v0.1.15...v0.1.16
[0.1.15]: https://github.com/taiki-e/semihosting/compare/v0.1.14...v0.1.15
[0.1.14]: https://github.com/taiki-e/semihosting/compare/v0.1.13...v0.1.14
[0.1.13]: https://github.com/taiki-e/semihosting/compare/v0.1.12...v0.1.13
[0.1.12]: https://github.com/taiki-e/semihosting/compare/v0.1.11...v0.1.12
[0.1.11]: https://github.com/taiki-e/semihosting/compare/v0.1.10...v0.1.11
[0.1.10]: https://github.com/taiki-e/semihosting/compare/v0.1.9...v0.1.10
[0.1.9]: https://github.com/taiki-e/semihosting/compare/v0.1.8...v0.1.9
[0.1.8]: https://github.com/taiki-e/semihosting/compare/v0.1.7...v0.1.8
[0.1.7]: https://github.com/taiki-e/semihosting/compare/v0.1.6...v0.1.7
[0.1.6]: https://github.com/taiki-e/semihosting/compare/v0.1.5...v0.1.6
[0.1.5]: https://github.com/taiki-e/semihosting/compare/v0.1.4...v0.1.5
[0.1.4]: https://github.com/taiki-e/semihosting/compare/v0.1.3...v0.1.4
[0.1.3]: https://github.com/taiki-e/semihosting/compare/v0.1.2...v0.1.3
[0.1.2]: https://github.com/taiki-e/semihosting/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/taiki-e/semihosting/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/taiki-e/semihosting/releases/tag/v0.1.0
