# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

No unreleased changes yet

## 1.0.3 - 2023-07-11

- Crate is deprecated, use `portable-atomic` instead.

## 1.0.2 - 2023-03-12

- Add MSP430 support.

## 1.0.1 - 2022-08-12

- Fix `AtomicPtr` accidentally not being available when not polyfilled.

## 1.0.0 - 2022-08-12

- Update to `critical-section` v1.0

## 0.1.11 - 2022-11-29

- Bump `critical-section` dependency from `0.2` to `1.0`.

  This is a breaking change if you were relying on the default implementations available on `critical-section 0.2.7` and earlier.
  They have been removed in `critical-section 0.2.8` because they were **unsound**, since there's no way to guarantee they're correct for the
  target in use (for example for multi-core embedded targets). Since `critical-section 0.2.8` just forwards to `1.0` now, we decided to change `atomic-polyfill` to use `1.0` directly.

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

## 0.1.10 - 2022-08-12

- Fix `AtomicPtr` accidentally not being available when not polyfilled.

## 0.1.9 - 2022-08-12

- Switch to only two polyfill levels.

The "CAS" level which uses atomic load/store and critical-section based CAS was not
sound, because `critical-section` guarantees only "no other critical section can run concurrently",
not "no other code can run concurrently". Therefore a CS-based CAS can still race a native atomic store.

## 0.1.8 - 2022-04-12

- Added AVR support.

## 0.1.7 - 2022-03-22

- Added support for xtensa (ESP chips), with and without ESP-IDF.
- Reexport `core::sync::atomic::*` as-is for unknown targets, to avoid build failures if they don't have full atomic support.

## 0.1.6 - 2022-02-08

- Add polyfill support for `thumbv4t` targets. (Nintendo Game Boy Advance)
- Added `get_mut()` to `AtomicBool`.
- Added `into_inner()` to all atomics
- Added `fmt::Debug` impl to `AtomicBool`, `AtomicPtr`.
- Added `fmt::Pointer` impl to `AtomicPtr`.
- Added `From<*mut T>` impl to `AtomicPtr`.
- Added `RefUnwindSafe` impl to all atomics.

## 0.1.5 - 2021-11-02

- Updated critical-section to v0.2.5. Fixes `std` implementation to allow reentrant (nested) critical sections. This would previously deadlock.

## 0.1.4 - 2021-09-20

- Added support for RISC-V.
- Added support for "full polyfill" level, where load/stores are polyfilled, not just CAS operations.
- Added support for `AtomicU64`, `AtomicI64`.

## 0.1.3 - 2021-08-07

- Only import `cortex-m` when needed (#4)
- Fix panic on `fetch_update` due to incorrect ordering (#5)

## 0.1.2 - 2021-03-29

- Added missing reexport of `fence` and `compiler_fence` in polyfilled mode.

## 0.1.1 - 2021-03-04

- Added polyfills for AtomicU8, AtomicU16, AtomicUsize, AtomicI8, AtomicI16, AtomicI32, AtomicIsize

## 0.1.0 - 2021-03-04

- First release
