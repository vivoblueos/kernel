[![crates.io](https://img.shields.io/crates/d/aarch64-cpu.svg)](https://crates.io/crates/aarch64-cpu)
[![crates.io](https://img.shields.io/crates/v/aarch64-cpu.svg)](https://crates.io/crates/aarch64-cpu)

# aarch64-cpu

Low level access to processors using the AArch64 execution state.

This project is developed and maintained by the [Cortex-A team][team].

## [Documentation](https://docs.rs/aarch64-cpu)

## Minimum Supported Rust Version (MSRV)

This crate is guaranteed to compile on current stable Rust.
It might compile with older versions but that may change in any new patch release.

## Usage

Please note that for using this crate's [register definitions](src/registers) (as provided by
`aarch64_cpu::registers::*`), you need to also import
`aarch64_cpu::registers::{Readable, Writeable}`.

### Example

Check out https://github.com/rust-embedded/rust-raspberrypi-OS-tutorials for usage examples. Listed
below is a snippet of `rust-raspberrypi-OS-tutorials`'s early boot code.

```rust
use aarch64_cpu::{asm, registers::*};

// Some parts omitted for brevity.

unsafe fn prepare_el2_to_el1_transition(
    virt_boot_core_stack_end_exclusive_addr: u64,
    virt_kernel_init_addr: u64,
) {
    // Enable timer counter registers for EL1.
    CNTHCTL_EL2.write(CNTHCTL_EL2::EL1PCEN::SET + CNTHCTL_EL2::EL1PCTEN::SET);

    // No offset for reading the counters.
    CNTVOFF_EL2.set(0);

    // Set EL1 execution state to AArch64.
    HCR_EL2.write(HCR_EL2::RW::EL1IsAarch64);

    // Set up a simulated exception return.
    SPSR_EL2.write(
        SPSR_EL2::D::Masked
            + SPSR_EL2::A::Masked
            + SPSR_EL2::I::Masked
            + SPSR_EL2::F::Masked
            + SPSR_EL2::M::EL1h,
    );
}
```

## Disclaimer

Descriptive comments in the source files are taken from the
[ARM Architecture Reference Manual ARMv8, for ARMv8-A architecture profile](https://documentation-service.arm.com/static/62ff43b0e95b0a633aff8a64?token=).

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
  http://www.apache.org/licenses/LICENSE-2.0)
- MIT License ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the
work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.

## Code of Conduct

Contribution to this crate is organized under the terms of the [Rust Code of
Conduct][CoC], the maintainer of this crate, the [Cortex-A team][team], promises
to intervene to uphold that code of conduct.

[CoC]: CODE_OF_CONDUCT.md
[team]: https://github.com/rust-embedded/wg#the-cortex-a-team
