# safe-mmio

[![crates.io page](https://img.shields.io/crates/v/safe-mmio.svg)](https://crates.io/crates/safe-mmio)
[![docs.rs page](https://docs.rs/safe-mmio/badge.svg)](https://docs.rs/safe-mmio)

This crate provides types for safe MMIO device access, especially in systems with an MMU.

This is not an officially supported Google product.

## Usage

### UniqueMmioPointer

The main type provided by this crate is `UniqueMmioPointer`. A `UniqueMmioPointer<T>` is roughly
equivalent to an `&mut T` for a memory-mapped IO device. Suppose you want to construct a pointer to
the data register of some UART device, and write some character to it:

```rust
use core::ptr::NonNull;
use safe_mmio::UniqueMmioPointer;

let mut data_register =
    unsafe { UniqueMmioPointer::<u8>::new(NonNull::new(0x900_0000 as _).unwrap()) };
unsafe {
    data_register.write_unsafe(b'x');
}
```

Depending on your platform this will either use `write_volatile` or some platform-dependent inline
assembly to perform the MMIO write.

### Safe MMIO methods

If you know that a particular MMIO field is safe to access, you can use the appropriate wrapper type
to mark that. In this case, suppose that the UART data register should only be written to:

```rust
use core::ptr::NonNull;
use safe_mmio::{fields::WriteOnly, UniqueMmioPointer};

let mut data_register: UniqueMmioPointer<WriteOnly<u8>> =
    unsafe { UniqueMmioPointer::new(NonNull::new(0x900_0000 as _).unwrap()) };
data_register.write(b'x');
```

### Grouping registers with a struct

In practice, most devices have more than one register. To model this, you can create a struct, and
then use the `field!` macro to project from a `UniqueMmioPointer` to the struct to a pointer to one
of its fields:

```rust
use core::ptr::NonNull;
use safe_mmio::{
    field,
    fields::{ReadOnly, ReadPure, ReadWrite, WriteOnly},
    UniqueMmioPointer,
};

#[repr(C)]
struct UartRegisters {
    data: ReadWrite<u8>,
    status: ReadPure<u8>,
    pending_interrupt: ReadOnly<u8>,
}

let mut uart_registers: UniqueMmioPointer<UartRegisters> =
    unsafe { UniqueMmioPointer::new(NonNull::new(0x900_0000 as _).unwrap()) };
field!(uart_registers, data).write(b'x');
```

Methods are also provided to go from a `UniqueMmioPointer` to an array or slice to its elements.

### Pure reads vs. side-effects

We distinguish between fields which for which MMIO reads may have side effects (e.g. popping a byte
from the UART's receive FIFO or clearing an interrupt status) and those for which reads are 'pure'
with no side-effects. Reading from a `ReadOnly` or `ReadWrite` field is assumed to have
side-effects, whereas reading from a `ReadPure` or `ReadPureWrite` must not. Reading from a
`ReadOnly` or `ReadWrite` field requires an `&mut UniqueMmioPointer` (the same as writing), whereas
reading from a `ReadPure` or `ReadPureWrite` field can be done with an `&UniqueMmioPointer` or
`&SharedMmioPointer`.

### Physical addresses

`UniqueMmioPointer` (and `SharedMmioPointer`) is used for a pointer to a device which is mapped into
the page table and accessible, i.e. a virtual address. Sometimes you may want to deal with the
physical address of a device, which may or may not be mapped in. For this you can use the
`PhysicalInstance` type. A `PhysicalInstance` doesn't let you do anything other than get the
physical address and size of the device's MMIO region, but is intended to convey ownership. There
should never be more than one `PhysicalInstance` pointer to the same device. This way your page
table management code can take a `PhysicalInstance<T>` and return a `UniqueMmioPointer<T>` when a
device is mapped into the page table.

## Comparison with other MMIO crates

There are a number of things that distinguish this crate from other crates providing abstractions
for MMIO in Rust.

1. We avoid creating references to MMIO address space. The Rust compiler is free to dereference
   references whenever it likes, so constructing references to MMIO address space (even temporarily)
   can lead to undefined behaviour. See https://github.com/rust-embedded/volatile-register/issues/10
   for more background on this.
2. We distinguish between MMIO reads which have side-effects (e.g. clearing an interrupt status, or
   popping from a queue) and those which don't (e.g. just reading some status). A read which has
   side-effects should be treated like a write and only be allowed from a unique pointer (passed via
   &mut) whereas a read without side-effects can safely be done via a shared pointer (passed via
   '&'), e.g. simultaneously from multiple threads.
3. On most platforms MMIO reads and writes can be done via `read_volatile` and `write_volatile`, but
   on aarch64 this may generate instructions which can't be virtualised. This is arguably
   [a bug in rustc](https://github.com/rust-lang/rust/issues/131894), but in the meantime we work
   around this by using inline assembly to generate the correct instructions for MMIO reads and
   writes on aarch64.

| Crate name                                                      | Last release   | Version | Avoids references | Distinguishes reads with side-effects | Works around aarch64 volatile bug | Model                               | Field projection           | Notes                                                                             |
| --------------------------------------------------------------- | -------------- | ------- | ----------------- | ------------------------------------- | --------------------------------- | ----------------------------------- | -------------------------- | --------------------------------------------------------------------------------- |
| safe-mmio                                                       | April 2025     | 0.2.5   | ✅                | ✅                                    | ✅                                | struct with field wrappers          | macro                      |
| [derive-mmio](https://crates.io/crates/derive-mmio)             | April 2025     | 0.4.0   | ✅                | ✅                                    | ❌                                | struct with derive macro            | through derive macro       |
| [volatile](https://crates.io/crates/volatile)                   | June 2024      | 0.6.1   | ✅                | ❌                                    | ❌                                | struct with derive macro            | macro or generated methods |
| [volatile-register](https://crates.io/crates/volatile-register) | October 2023   | 0.2.2   | ❌                | ❌                                    | ❌                                | struct with field wrappers          | manual (references)        |
| [tock-registers](https://crates.io/crates/tock-registers)       | September 2023 | 0.9.0   | ❌                | ❌                                    | ❌                                | macros to define fields and structs | manual (references)        | Also covers CPU registers, and bitfields                                          |
| [mmio](https://crates.io/crates/mmio)                           | May 2021       | 2.1.0   | ✅                | ❌                                    | ❌                                | only deals with individual fields   | ❌                         |
| [rumio](https://crates.io/crates/rumio)                         | March 2021     | 0.2.0   | ✅                | ❌                                    | ❌                                | macros to define fields and structs | generated methods          | Also covers CPU registers, and bitfields                                          |
| [vcell](https://crates.io/crates/vcell)                         | January 2021   | 0.1.3   | ❌                | ❌                                    | ❌                                | plain struct                        | manual (references)        |
| [register](https://crates.io/crates/register)                   | January 2021   | 1.0.2   | ❌                | ❌                                    | ❌                                | macros to define fields and structs | manual (references)        | Deprecated in favour of tock-registers. Also covers CPU registers, and bitfields. |

## License

Licensed under either of

- Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license
  ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contributing

If you want to contribute to the project, see details of
[how we accept contributions](CONTRIBUTING.md).
