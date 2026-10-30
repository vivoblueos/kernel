# critical-section
[![crates.io](https://img.shields.io/crates/d/critical-section.svg)](https://crates.io/crates/critical-section)
[![crates.io](https://img.shields.io/crates/v/critical-section.svg)](https://crates.io/crates/critical-section)
[![Documentation](https://docs.rs/critical-section/badge.svg)](https://docs.rs/critical-section)

This project is developed and maintained by the [HAL team][team].

A critical section that works everywhere!

When writing software for embedded systems, it's common to use a "critical section"
as a basic primitive to control concurrency. A critical section is essentially a
mutex global to the whole process, that can be acquired by only one thread at a time.
This can be used to protect data behind mutexes, to [emulate atomics](https://crates.io/crates/portable-atomic) in
targets that don't support them, etc.

There's a wide range of possible implementations depending on the execution environment:
- For bare-metal single core, disabling interrupts in the current (only) core.
- For bare-metal multicore, disabling interrupts in the current core and acquiring a hardware spinlock to prevent other cores from entering a critical section concurrently.
- For bare-metal using a RTOS, using library functions for acquiring a critical section, often named "scheduler lock" or "kernel lock".
- For bare-metal running in non-privileged mode, calling some system call is usually needed.
- For `std` targets, acquiring a global `std::sync::Mutex`.

Libraries often need to use critical sections, but there's no universal API for this in `core`. This leads
library authors to hard-code them for their target, or at best add some `cfg`s to support a few targets.
This doesn't scale since there are many targets out there, and in the general case it's impossible to know
which critical section implementation is needed from the Rust target alone. For example, the `thumbv7em-none-eabi` target
could be cases 1-4 from the above list.

This crate solves the problem by providing this missing universal API.

- It provides functions `acquire`, `release` and `with` that libraries can directly use.
- It provides a way for any crate to supply an implementation. This allows "target support" crates such as architecture crates (`cortex-m`, `riscv`), RTOS bindings, or HALs for multicore chips to supply the correct implementation so that all the crates in the dependency tree automatically use it.

## Usage in `no-std` binaries.

First, add a dependency on a crate providing a critical section implementation. Enable the `critical-section-*` Cargo feature if required by the crate.

Implementations are typically provided by either architecture-support crates, HAL crates, and OS/RTOS bindings, including:

* The [`cortex-m`] crate provides an implementation for all single-core Cortex-M microcontrollers via its `critical-section-single-core` feature
* The [`riscv`] crate provides an implementation for all single-hart RISC-V microcontrollers via its `critical-section-single-hart` feature
* The [`msp430`] crate provides an implementation for all MSP430 microcontrollers via its `critical-section-single-core` feature
* The [`rp2040-hal`] crate provides a multi-core-safe critical section for the RP2040 microcontroller via its `critical-section-impl` feature
* The [`avr-device`] crate provides an implementation for all AVR microcontrollers via its `critical-section-impl` feature
* The [`esp-hal-common`] crate provides an implementation for ESP32 microcontrollers which is used by the ESP HALs
* The [`embassy-rp`] crate provides a multi-core-safe critical section for the RP2040 microcontroller via its `critical-section-impl` feature
* The [`nrf-softdevice`] crate provides a critical section that's compatible with the nRF soft-device firmware via its `critical-section-impl` feature

[`cortex-m`]: https://crates.io/crates/cortex-m
[`riscv`]: https://crates.io/crates/riscv
[`msp430`]: https://crates.io/crates/msp430
[`rp2040-hal`]: https://crates.io/crates/rp2040-hal
[`avr-device`]: https://crates.io/crates/avr-device
[`esp-hal-common`]: https://crates.io/crates/esp-hal-common
[`embassy-rp`]: https://docs.embassy.dev/embassy-rp
[`nrf-softdevice`]: https://docs.embassy.dev/nrf-softdevice

For example, for single-core Cortex-M targets, you can use:

```toml
[dependencies]
cortex-m = { version = "0.7.6", features = ["critical-section-single-core"]}
```

Then you can use `critical_section::with()`.

```rust
use core::cell::Cell;
use critical_section::Mutex;

static MY_VALUE: Mutex<Cell<u32>> = Mutex::new(Cell::new(0));

critical_section::with(|cs| {
    // This code runs within a critical section.

    // `cs` is a token that you can use to "prove" that to some API,
    // for example to a `Mutex`:
    MY_VALUE.borrow(cs).set(42);
});

# #[cfg(not(feature = "std"))] // needed for `cargo test --features std`
# mod no_std {
#     struct MyCriticalSection;
#     critical_section::set_impl!(MyCriticalSection);
#     unsafe impl critical_section::Impl for MyCriticalSection {
#         unsafe fn acquire() -> () {}
#         unsafe fn release(token: ()) {}
#     }
# }
```

## Usage in `std` binaries.

Add the `critical-section` dependency to `Cargo.toml` enabling the `std` feature. This makes the `critical-section` crate itself
provide an implementation based on `std::sync::Mutex`, so you don't have to add any other dependency.

```toml
[dependencies]
critical-section = { version = "1.1", features = ["std"]}
```

## Usage in libraries

If you're writing a library intended to be portable across many targets, simply add a dependency on `critical-section`
and use `critical_section::free` and/or `Mutex` as usual.

**Do not** add any dependency supplying a critical section implementation. Do not enable any `critical-section-*` Cargo feature.
This has to be done by the end user, enabling the correct implementation for their target.

**Do not** enable any Cargo feature in `critical-section`.

## Usage in `std` tests for `no-std` libraries.

If you want to run `std`-using tests in otherwise `no-std` libraries, enable the `std` feature in `dev-dependencies` only.
This way the main target will use the `no-std` implementation chosen by the end-user's binary, and only the test targets
will use the `std` implementation.

```toml
[dependencies]
critical-section = "1.1"

[dev-dependencies]
critical-section = { version = "1.1", features = ["std"]}
```

## Providing an implementation

Crates adding support for a particular architecture, chip or operating system should provide a critical section implementation.
It is **strongly recommended** to gate the implementation behind a feature, so the user can still use another implementation
if needed (having two implementations in the same binary will cause linking to fail).

Add the dependency, and a `critical-section-*` feature to your `Cargo.toml`:

```toml
[features]
# Enable critical section implementation that does "foo"
critical-section-foo = ["critical-section/restore-state-bool"]

[dependencies]
critical-section = { version = "1.0", optional = true }
```

Then, provide the critical implementation like this:

```rust
# #[cfg(not(feature = "std"))] // needed for `cargo test --features std`
# mod no_std {
// This is a type alias for the enabled `restore-state-*` feature.
// For example, it is `bool` if you enable `restore-state-bool`.
use critical_section::RawRestoreState;

struct MyCriticalSection;
critical_section::set_impl!(MyCriticalSection);

unsafe impl critical_section::Impl for MyCriticalSection {
    unsafe fn acquire() -> RawRestoreState {
        // TODO
    }

    unsafe fn release(token: RawRestoreState) {
        // TODO
    }
}
# }
```

## Troubleshooting

### Undefined reference errors

If you get an error like these:

```not_rust
undefined reference to `_critical_section_1_0_acquire'
undefined reference to `_critical_section_1_0_release'
```

it is because you (or a library) are using `critical_section::with` without providing a critical section implementation.
Make sure you're depending on a crate providing the implementation, and have enabled the `critical-section-*` feature in it if required. See the `Usage` section above.

The error can also be caused by having the dependency but never `use`ing it. This can be fixed by adding a dummy `use`:

```rust,ignore
use the_cs_impl_crate as _;
```

### Duplicate symbol errors

If you get errors like these:

```not_rust
error: symbol `_critical_section_1_0_acquire` is already defined
```

it is because you have two crates trying to provide a critical section implementation. You can only
have one implementation in a program.

You can use `cargo tree --format '{p} {f}'` to view all dependencies and their enabled features. Make sure
that in the whole dependency tree, exactly one implementation is provided.

Check for multiple versions of the same crate as well. For example, check the `critical-section-single-core`
feature is not enabled for both `cortex-m` 0.7 and 0.8.

## Why not generics?

An alternative solution would be to use a `CriticalSection` trait, and make all
code that needs acquiring the critical section generic over it. This has a few problems:

- It would require passing it as a generic param to a very big amount of code, which
would be quite unergonomic.
- It's common to put `Mutex`es in `static` variables, and `static`s can't
be generic.
- It would allow mixing different critical section implementations in the same program,
which would be unsound.

## Minimum Supported Rust Version (MSRV)

This crate is guaranteed to compile on the following Rust versions:

- If the `std` feature is not enabled: stable Rust 1.54 and up.
- If the `std` feature is enabled: stable Rust 1.63 and up.

It might compile with older versions but that may change in any new patch release.

See [here](docs/msrv.md) for details on how the MSRV may be upgraded.

## License

This work is licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
  <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

## Code of Conduct

Contribution to this crate is organized under the terms of the [Rust Code of
Conduct][CoC], the maintainer of this crate, the [HAL team][team], promises
to intervene to uphold that code of conduct.

[CoC]: CODE_OF_CONDUCT.md
[team]: https://github.com/rust-embedded/wg#the-hal-team
