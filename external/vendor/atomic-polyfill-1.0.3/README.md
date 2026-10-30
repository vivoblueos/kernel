# ⚠️ THIS CRATE IS DEPRECATED ⚠️

**Use [`portable-atomic`](https://crates.io/crates/portable-atomic) instead.** It supports many more architectures and more efficient ways of emulating atomics.

`portable-atomic` with the `critical-section` feature is a drop-in replacement. It uses the `critical-section` crate to ensure locking, just like `atomic-polyfill`.

However, if your chip is single-core, you might want to enable the `unsafe-assume-single-core` feature instead. It makes `portable-atomic` emulate atomics by disabling interrupts.
It is faster than using a `critical-section` implementation that disables interrupts, because it allows disabling them only on CAS operations, not in load/store operations.

**If you're writing a library**, add a dependency on `portable-atomic` but do NOT enable any feature on it. Let the end user of your library enable the right features for their target.
If you enable features, you're taking their choice away.

-----

# atomic-polyfill

[![Documentation](https://docs.rs/atomic-polyfill/badge.svg)](https://docs.rs/atomic-polyfill)

This crate polyfills atomics on targets where they're not available, using critical sections. It is intended to be a drop-in replacement for `core::sync::atomic`.

There are two "levels" of polyfilling:
- Native: No polyfilling is performed, the native `core::sync::atomic::AtomicXX` is reexported.
- Full: Both load/store and compare-and-set operations are polyfilled.

Polyfilling requires a [`critical-section`](https://github.com/rust-embedded/critical-section) implementation for the current target. Check the `critical-section` README for details.

## Target support

The right polyfill level is automatically picked based on the target and the atomic width:

| Target             | Level            | Level for u64/i64 |
|--------------------|------------------|-------------------|
| thumbv4t           | Full             | Full              |
| thumbv6m           | Full             | Full              |
| thumbv7*, thumbv8* | Native           | Full              |
| riscv32imc         | Full             | Full              |
| riscv32imac        | Native           | Full              |
| xtensa-*-espidf    | Native           | Native            |
| xtensa-esp32-*     | Native           | Full              |
| xtensa-esp32s2-*   | Full             | Full              |
| xtensa-esp32s3-*   | Native           | Full              |
| xtensa-esp8266-*   | Full             | Full              |
| AVR                | Full             | Full              |

For targets not listed above, `atomic-polyfill` assumes nothing and reexports `core::sync::atomic::*`. No polyfilling is done. PRs for polyfilling more targets are welcome :)

## Minimum Supported Rust Version (MSRV)

MSRV is currently **Rust 1.54**. MSRV may be upgraded at any new patch release as long
as latest stable Rust is supported.

## License

This work is licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
  http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
