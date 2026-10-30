# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

## [v0.15.0] - 2025-09-08

### Added

- New convenience  `try_new` and `new` associated functions for `Mtvec` and `Stvec`.
- New methods and functions for enabling core interrupts in the `mie` and `sie` registers
  using the `riscv_pac::CoreInterruptNumber` trait.
- New `riscv::interrupt::{is_interrupt_enabled, disable_interrupt, enable_interrupt}` functions.
- New methods and functions for dealing with pending interrupts in `mip` and `sip` registers
  using the `riscv_pac::CoreInterruptNumber` trait.
- New `riscv::interrupt::is_interrupt_pending` function.
- New `riscv::register::xip::clear_pending` atomic function for `mip` and `sip` registers.
  This function is marked as `unsafe`, as its availability depends both on the target chip
  and the target interrupt source.
- Add `mseccfg` CSR
- Add `mseccfgh` CSR

### Changed

- Use `cfg(any(target_arch = "riscv32", target_arch = "riscv64"))` instead of `cfg(riscv)`.
- `riscv::pac_enum(unsafe CoreInterrupt)` now locates the vector table at the `.trap.vector`
  section instead of `.trap`.
- Allow all bits to be set in Mcause::from_bits on 64-bit targets.

### Removed

- Removed custom build script, as `cfg(riscv)` is no longer necessary.
- All the fields of `Mip` and `Sip` CSR proxies are now read-only. This change is motivated
  to avoid clearing unwanted interrupts triggered between CSR reads and CSR writes.

## [v0.14.0] - 2025-06-10

### Added

- CSR helper macro `write_composite_csr` for writing 64-bit CSRs on 32-bit targets.
- Write utilities for `mcycle`, `minstret`
- Add `senvcfg` CSR
- Add `scontext` CSR
- Add `mconfigptr` CSR
- Bump MSRV to 1.67.0 for `log` to `ilog` name change
- Add `mtval2` CSR

### Changed

- Simplify `riscv::interrupt::machine::nested`

## [v0.13.0] - 2025-02-18

### Added

- CSR helper macro to check for platform implementation

### Changed

- Make all CSR writes `unsafe` by default (#209)
- Use `RISCV_MTVEC_ALIGN` to control the alignment constraint of the vector table
- Simplify register macros with `cfg` field
- Align assembly functions with `cortex-m`
- Use CSR helper macros to define `marchid` register
- Re-use `try_*` functions in `mcountinhibit`
- Use CSR helper macros to define `mcause` register
- Use CSR helper macros to define `medeleg` register
- Use CSR helper macros to define `mideleg` register
- Use CSR helper macros to define `mcounteren` register
- Use CSR helper macros to define `mie` register
- Use CSR helper macros to define `mimpid` register
- Use CSR helper macros to define `misa` register
- Use CSR helper macros to define `mip` register
- Use CSR helper macros to define `mstatus` register
- Use CSR helper macros to define `mstatush` register
- Use CSR helper macros to define `mtvec` register
- Use CSR helper macros to define `mtvendorid` register
- Use CSR helper macros to define `satp` register
- Use CSR helper macros to define `pmpcfgx` field types
- Use CSR helper macros to define `scause` field types
- Use CSR helper macros to define `sie` register
- Use CSR helper macros to define `scounteren` field types
- Use CSR helper macros to define `sip` register
- Use CSR helper macros to define `sstatus` field types
- Use CSR helper macros to define `stvec` field types
- Add remaining `pmpcfg` CSRs from RISC-V privileged spec

## [v0.12.1] - 2024-10-20

### Changed

- Update critical-section to 1.2.0

## [v0.12.0] - 2024-10-19

### Added

- `riscv-macros` crate for `riscv-pac` enums.
- Bump MSRV to 1.61.
- Implementation of `riscv-pac` traits for `Interrupt` and `Exception` enums.
- Tests for the `riscv-pac` trait implementations of `Interrupt` and `Exception` enums.
- Add `Mcause::from(usize)` for use in unit tests
- Add `Mstatus::from(usize)` for use in unit tests
- Add `Mstatus.bits()`
- Add `Eq` and `PartialEq` for `pmpcfgx::{Range, Permission}`
- Add `Mstatus::update_*` helpers to manipulate Mstatus values without touching
  the CSR
- Export `riscv::register::macros` module macros for external use
- Add `riscv::register::mcountinhibit` module for `mcountinhibit` CSR
- Add `Mcounteren` in-memory update functions 
- Add `Mstatus` vector extension support
- Add fallible counterparts to all functions that `panic`
- Add `riscv-pac` as a dependency
- Add CSR-defining macros to create in-memory types

### Fixed

- Fixed `sip::set_ssoft` and `sip::clear_ssoft` using wrong address
- Fixed assignment in `mstatus` unit tests.
- delay implementation does not use binary labels in inline assembly.

## [v0.11.1] - 2024-02-15

### Changed

- Made `asm::wfi`, `fence`, `fence_i` and `sfence` safe (ie, removed `unsafe` from their definitions)
- Made `cfg` variable selection more robust for custom targets

## [v0.11.0] - 2024-01-14

### Added

- Add `asm::ecall()`, a wrapper for implementing an `ecall` instruction
- Add `nested` function for nested ISRs in `interrupt::machine` and `interrupt::supervisor`
- `s-mode` feature for reexporting `interrupt::machine` or `interrupt::supervisor` to `interrupt`
- Support for supervisor-level interrupts in `interrupt::supervisor`
- Add CI workflow to check that CHANGELOG.md file has been modified in PRs
- Add `read_csr_as_rv32`, `set_rv32`, and `clear_rv32` macros
- Add `mstatus::uxl` and `mstatus::sxl`
- Add `mstatus::ube`, `mstatus::sbe`, and `mstatus::mbe` endianness bit fields
- Add `mstatush` registers (RISCV-32 only)
- Add `asm::fence()`, a wrapper for implementing a `fence` instruction
- Add `asm::fence_i()`, a wrapper for implementing a `fence.i` instruction
- Add `TryFrom` implementation for `mcause::{Interrupt, Exception}` and `scause::{Interrupt, Exception}`

### Changed

- Cargo workspace for riscv and riscv-rt
- Update `embedded-hal` dependency to v1.0.0 (bumps MSRV to 1.60)
- `misa::MXL` renamed to `misa::XLEN`
- Removed `bit_field` dependency
- CI actions updated. They now use `checkout@v3` and `dtolnay/rust-toolchain`.
- `mcause::{Interrupt, Exception}` and `scause::{Interrupt, Exception}` now implement `From` trait for `usize`
- Set safety of `asm::nop` and `asm::delay` functions to safe.

### Fixed

- Fix `scause::Exception` missing `LoadMisaligned`
- Fix `scause::Exception` missing `SupervisorEnvCall`
- Removed user-level interrupts from `mcause::Interrupt` and `scause::Interrupt`
- Removed user-level interrupts from `mstatus`
- Removed machine environment call delegation from `medeleg`
- Removed user-level interrupts from machine and supervisor mode interrupt-related registers.

### Removed

- User mode registers removed, as they are no longer supported in RISC-V
- FCSR register operations removed to avoid UB (#148)

## [v0.10.1] - 2023-01-18

### Fixed

- Fix implementation for `SingleHartCriticalSection`

## [v0.10.0] - 2022-11-09

### Added

- `critical-section-single-hart` feature which provides an implementation for the `critical_section` crate for single-hart systems, based on disabling all interrupts.

## [v0.9.0] - 2022-10-06

### Fixed

- Fix `asm::delay()` to ensure count register is always reloaded
- Fix reading marchid and mimpid (#107)

### Removed
- `set_msoft`, `clear_msoft`, `set_mtimer` and `clear_mtimer` removed as part of fixing issue #62

## [v0.8.0] - 2022-04-20

### Added

- Add `#[cfg(riscv32)]` to `pmpcfg1` and `pmpcfg3` modules
- Add enums `Range`, `Permission` for PMP configuration
- Add `set_pmp()` and `clear_pmp()` functions to pmpcfg(x) modules
- Add struct `Pmpcsr` and is returned from `pmpcfgx::read()`
- Add `singleton!` macro
- Add delay structure and methods using embedded-hal traits and `mcycle` register
- Add `asm::delay()` function for assembly-based busy-loops
- Add `asm::nop()`, a wrapper for implementing a `nop` instruction
- Add missing `#[inline]` attribute to register reads, type conversations and `interrupt::free`

### Changed

- Use new `asm!` instead of `llvm_asm!`
- Change `pmpcfgx::read()` macro to `read_csr_as!()` from `read_csr_as_usize!()`
- Inline assembly is now always used
- Update Minimum Supported Rust Version to 1.59

### Fixed

- Fix `sfence.vma` operand order

### Removed

- Remove `inline-asm` feature which is now always enabled

## [v0.7.0] - 2021-07-29

### Added

- Add `medeleg` register
- Add `cycle[h]`, `instret[h]` and `mcounteren`
- Add additional binaries for floating-point ABIs
- Add support for `mxr`
- Add support for `mprv`

### Changed

- Fix `scause::set`
- Various formatting and comment fixes
- Update `bare-metal` to `v1.0.0` removing `Nr` trait
- Build targets on `docs.rs` are now RISC-V targets other than default ones

## [v0.6.0] - 2020-06-20

### Changed

- `Mtvec::trap_mode()`, `Stvec::trap_mode()` and `Utvec::trap_mode()` functions now return `Option<TrapMode>` (breaking change)
- Updated Minimum Supported Rust Version to 1.42.0
- Use `llvm_asm!` instead of `asm!`

### Removed

- vexriscv-specific registers were moved to the `vexriscv` crate

## [v0.5.6] - 2020-03-14

### Added

- Added vexriscv-specific registers

## [v0.5.5] - 2020-02-28

### Added

- Added `riscv32i-unknown-none-elf` target support
- Added user trap setup and handling registers
- Added write methods for the `mip` and `satp` registers
- Added `mideleg` register
- Added Changelog

### Changed

- Fixed MSRV by restricting the upper bound of `bare-metal` version

[Unreleased]: https://github.com/rust-embedded/riscv/compare/v0.10.1...HEAD
[v0.10.1]: https://github.com/rust-embedded/riscv/compare/v0.10.0...v0.10.1
[v0.10.0]: https://github.com/rust-embedded/riscv/compare/v0.9.0...v0.10.0
[v0.9.0]: https://github.com/rust-embedded/riscv/compare/v0.8.0...v0.9.0
[v0.8.0]: https://github.com/rust-embedded/riscv/compare/v0.7.0...v0.8.0
[v0.7.0]: https://github.com/rust-embedded/riscv/compare/v0.6.0...v0.7.0
[v0.6.0]: https://github.com/rust-embedded/riscv/compare/v0.5.6...v0.6.0
[v0.5.6]: https://github.com/rust-embedded/riscv/compare/v0.5.5...v0.5.6
[v0.5.5]: https://github.com/rust-embedded/riscv/compare/v0.5.4...v0.5.5
