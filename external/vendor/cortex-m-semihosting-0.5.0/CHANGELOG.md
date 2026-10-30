# Change Log

All notable changes to this project will be documented in this file.
This project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

## [v0.5.0] - 2022-03-01

- Always use inline-asm, requiring Rust 1.59.
- Removed inline-asm feature.

## [v0.4.1] - 2020-10-20

0.4.1 was yanked because the pre-built binaries contain conflicting symbols
with a supported version of cortex-m.

- Fix missing prebuilt binaries (#271)

## [v0.4.0] - 2020-10-14

v0.4.0 was yanked because it did not include the required pre-built binaries
in the final crate.

- Moved into cortex-m repository
- Merge `HStdout` and `HStderr` into one type: `HostStream`
- Support cortex-m v0.7
- Semihosting macros no longer return a Result, instead errors are ignored.

## [v0.3.7] - 2020-12-02

- Replaces the yanked v0.3.6 by reverting #48, so the semihosting macros
  continue to return a Result.

## [v0.3.6] - 2020-12-01

v0.3.6 was yanked because it incorrectly included #48, which was a breaking
change.

### Added

- Update cortex-m dependency to support version 0.7.
- Add `no-semihosting` feature to disable all semihosting calls.

## [v0.3.5] - 2019-08-29

### Added

- Adds a feature to work around JLink quirks
- Adds a dbg! macro using heprintln
- Added thumbv8m.main support on stable

### Fixed

- Now Rust 2018 edition

## [v0.3.4] - 2019-08-13

### Fixed

- Support for thumbv8 mainline hf target

## [v0.3.3] - 2019-04-22

### Added

- Adds support for thumbv8 and cortex-m v0.6.0

## [v0.3.2] - 2018-11-04

### Added

- Added a family of `hprint` macros for printing to the host standard output /
  error via globally shared `HStdout` / `HStderr` handles .

## [v0.3.1] - 2018-08-27

### Changed

- This crate no longer depends on `arm-none-eabi-gcc`.

## [v0.3.0] - 2018-05-10

### Changed

- [breaking-change] `inline-asm` is no longer a default feature (i.e. a feature that's enabled by
  default). The consequence is that this crate now compiles on 1.27 (beta) by default, and opting
  into `inline-asm` requires nightly.

## [v0.2.1] - 2018-04-25

### Added

- An opt-out "inline-asm" Cargo feature. When this feature is disabled semihosting is implemented
  using an external assembly file instead of using the unstable inline assembly (`asm!`) feature
  meaning that this crate can be compiled on stable.

## [v0.2.0] - 2017-07-07

### Added

- `exit` and `report_exception` syscalls

- `HStdout` and `HStderr` structs that represent handles to the host stdout and
  stderr stream respectively.

### Changed

- [breaking-change] The `io` module has been renamed to `hio` to reflect that
  this is I/O *on the host*.

### Removed

- [breaking-change] the family of `write` functions in the `io` module. Instead
  use `HStdout` / `HStderr` and its `write_all` method and `fmt::Write`
  implementation.

- [breaking-change] the `hprint!` family of macros. Instead use `HStdout` and
  the standard `write!` macro.

## [v0.1.3] - 2017-02-27

### Added

- A family of `ewrite` functions and `ehprint!` macros to write to the host's
  stderr.

### Fixed

- `write_all` logic when a single write doesn't write all the buffer bytes

## [v0.1.2] - 2017-02-15

### Fixed

- the `hprintln!` macro when called without arguments.

## [v0.1.1] - 2017-01-22

### Added

- Expose a family of `write` functions to write to the host's stdout without
  going through the `hprint!` macros.

## v0.1.0 - 2017-01-22

- Initial release

[Unreleased]: https://github.com/rust-embedded/cortex-m/compare/c-m-sh-v0.5.0...HEAD
[v0.5.0]: https://github.com/rust-embedded/cortex-m/compare/c-m-sh-v0.4.1...c-m-sh-v0.5.0
[v0.4.1]: https://github.com/rust-embedded/cortex-m/compare/c-m-sh-v0.4.0...c-m-sh-v0.4.1
[v0.4.0]: https://github.com/rust-embedded/cortex-m/compare/c-m-sh-v0.3.5...c-m-sh-v0.4.0
[v0.3.7]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.3.6...v0.3.7
[v0.3.6]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.3.5...v0.3.6
[v0.3.5]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.3.4...v0.3.5
[v0.3.4]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.3.3...v0.3.4
[v0.3.3]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.3.2...v0.3.3
[v0.3.2]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.3.1...v0.3.2
[v0.3.1]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.3.0...v0.3.1
[v0.3.0]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.2.1...v0.3.0
[v0.2.1]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.2.0...v0.2.1
[v0.2.0]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.1.3...v0.2.0
[v0.1.3]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.1.2...v0.1.3
[v0.1.2]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.1.1...v0.1.2
[v0.1.1]: https://github.com/rust-embedded/cortex-m-semihosting/compare/v0.1.0...v0.1.1
