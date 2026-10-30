# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

No unreleased changes yet

## [v1.2.0] - 2024-10-16

- Soundness fix: ensure the `CriticalSection` token is not `Send` or `Sync`, so that it can only be used in the thread that acquired it. [#55](https://github.com/rust-embedded/critical-section/issues/55)
- Soundness fix: Fix aliasing `&mut` in the `std` implementation. [#46](https://github.com/rust-embedded/critical-section/pull/46)
- Fix build with `restore-state-usize`. [#50](https://github.com/rust-embedded/critical-section/pull/50)

## [v1.1.3] - 2024-08-22

- Added option to use a `usize` sized restore state

## [v1.1.2] - 2023-08-09

- Clarified that `acquire()` must provide ordering guarantees
- Updated atomic-polyfill reference to point to portable-atomic instead
- Improved documentation for `Mutex` example
- Added list of some known implementations

## [v1.1.1] - 2022-09-13

- On the `std` implementation, panicking inside the `critical_section::with()` closure no longer accidentally leaves the critical section locked (#26).

## [v1.1.0] - 2022-08-17

- Added built-in critical section implementation using `std::sync::Mutex`, enabled by the `std` Cargo feature.
- MSRV changed to `1.54` when `std` feature is disabled, `1.63` when enabled.

## [v1.0.0] - 2022-08-10

- Improved docs.

## [v1.0.0-alpha.2] - 2022-07-28

- Change name of the `extern fn`s to avoid clash with critical-section 0.2.

## [v1.0.0-alpha.1] - 2022-07-28

Breaking changes:

- Removed all builtin impls. These are going to be provided by platform-support crates now.
- Renamed `custom_impl!` to `set_impl!`.
- RestoreState is now an opaque struct for the user, and a transparent `RawRestoreState` type alias for impl writers.
- RestoreState type is now configurable with Cargo features. Default is `()`. (previously it was fixed to `u8`.)
- Added own `CriticalSection` and `Mutex` types, instead of reexporting them from `bare_metal`.

## [v0.2.8] - 2022-11-29

- Implemented critical-section by forwarding to version 1.1.1

Breaking changes:

- `acquire` and `release` are only implemented if the restore-state used by
  version 1.1.1 is an u8 or smaller.
- No default critical-section implementation is provided.

Those breaking changes are necessary because versions <= 0.2.7 were unsound, and that
was impossible to fix without a breaking change.

This version is meant to minimize that breaking change. However, all
users are encouraged to upgrade to critical-section 1.1.

If you're seeing a linker error like `undefined symbol: _critical_section_1_0_acquire`, you're affected. To fix it:

- If your target supports `std`: Add the `critical-section` dependency to `Cargo.toml` enabling the `std` feature.

  ```toml
  [dependencies]
  critical-section = { version = "1.1", features = ["std"]}
  ```

- For single-core Cortex-M targets in privileged mode:
  ```toml
  [dependencies]
  cortex-m = { version = "0.7.6", features = ["critical-section-single-core"]}
  ```

- For single-hart RISC-V targets in privileged mode:
  ```toml
  [dependencies]
  riscv = { version = "0.10", features = ["critical-section-single-hart"]}
  ```

- For other targets: check if your HAL or architecture-support crate has a `critical-section 1.0` implementation available. Otherwise, [provide your own](https://github.com/rust-embedded/critical-section#providing-an-implementation).


## [v0.2.7] - 2022-04-08

- Add support for AVR targets.

## [v0.2.6] - 2022-04-02

- Improved docs.

## [v0.2.5] - 2021-11-02

- Fix `std` implementation to allow reentrant (nested) critical sections. This would previously deadlock.

## [v0.2.4] - 2021-09-24

- Add support for 32bit RISC-V targets.

## [v0.2.3] - 2021-09-13

- Use correct `#[vcfg]` for `wasm` targets.

## [v0.2.2] - 2021-09-13

- Added support for `wasm` targets.

## [v0.2.1] - 2021-05-11

- Added critical section implementation for `std`, based on a global Mutex.

## [v0.2.0] - 2021-05-10

- Breaking change: use `CriticalSection<'_>` instead of `&CriticalSection<'_>`

## v0.1.0 - 2021-05-10

- First release

[Unreleased]: https://github.com/rust-embedded/critical-section/compare/v1.2.0...HEAD
[v1.2.0]: https://github.com/rust-embedded/critical-section/compare/v1.1.3...v1.2.0
[v1.1.3]: https://github.com/rust-embedded/critical-section/compare/v1.1.2...v1.1.3
[v1.1.2]: https://github.com/rust-embedded/critical-section/compare/v1.1.1...v1.1.2
[v1.1.1]: https://github.com/rust-embedded/critical-section/compare/v1.1.0...v1.1.1
[v1.1.0]: https://github.com/rust-embedded/critical-section/compare/v1.0.0...v1.1.0
[v1.0.0]: https://github.com/rust-embedded/critical-section/compare/v1.0.0-alpha.2...v1.0.0
[v1.0.0-alpha.2]: https://github.com/rust-embedded/critical-section/compare/v1.0.0-alpha.1...v1.0.0-alpha.2
[v1.0.0-alpha.1]: https://github.com/rust-embedded/critical-section/compare/v0.2.7...v1.0.0-alpha.1
[v0.2.8]: https://github.com/rust-embedded/critical-section/compare/v0.2.7...v0.2.8
[v0.2.7]: https://github.com/rust-embedded/critical-section/compare/v0.2.6...v0.2.7
[v0.2.6]: https://github.com/rust-embedded/critical-section/compare/v0.2.5...v0.2.6
[v0.2.5]: https://github.com/rust-embedded/critical-section/compare/v0.2.4...v0.2.5
[v0.2.4]: https://github.com/rust-embedded/critical-section/compare/v0.2.3...v0.2.4
[v0.2.3]: https://github.com/rust-embedded/critical-section/compare/v0.2.2...v0.2.3
[v0.2.2]: https://github.com/rust-embedded/critical-section/compare/v0.2.1...v0.2.2
[v0.2.1]: https://github.com/rust-embedded/critical-section/compare/v0.2.0...v0.2.1
[v0.2.0]: https://github.com/rust-embedded/critical-section/compare/v0.1.0...v0.2.0
