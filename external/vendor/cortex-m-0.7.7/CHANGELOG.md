# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

## [v0.7.7] - 2023-01-03

- Add missing documentation for `critical-section-single-core` feature added
  in v0.7.6.

## [v0.7.6] - 2022-08-12

- Added `critical-section-single-core` feature which provides an implementation for the `critical-section` crate for single-core systems, based on disabling all interrupts. (#448)

## [v0.7.5] - 2022-05-15

### Deprecated
- the `ptr()` function on all peripherals register blocks in favor of
  the associated constant `PTR` (#386).

### Changed

- The `inline-asm` feature no longer requires a nightly Rust compiler, but
  does require Rust 1.59 or above.

### Fixed
- Fixed `singleton!()` statics sometimes ending up in `.data` instead of `.bss` (#364, #380).
  (Backported from upcoming 0.8 release).

## [v0.7.4] - 2021-12-31

### Added

- Added support for additional DWT counters (#349)
    - CPI counter
    - Exception overhead counter
    - LSU counter
    - Folded-instruction counter
- Added `DWT.set_cycle_count` (#347).
- Added support for the Cortex-M7 TCM and cache access control registers.
  There is a feature `cm7` to enable access to these (#352).
- Add derives for serde, Hash, and PartialOrd to VectActive behind feature
  gates for host-platform use (#363).
- Support host platforms besides x86_64 (#369).
- Added `delay::Delay::with_source`, a constructor that lets you specify
  the SysTick clock source (#374).

### Fixed

- Fix incorrect AIRCR PRIGROUP mask (#338, #339).
- Fix nightly users of inline-asm breaking now that the asm macro is removed
  from the prelude (#372).

### Deprecated

- `DWT::get_cycle_count` has been deprecated in favor of `DWT::cycle_count`.
  This change was made for consistency with the [C-GETTER] convention. (#349)

[C-GETTER]: https://rust-lang.github.io/api-guidelines/naming.html#c-getter

## [v0.7.3] - 2021-07-03

### Fixed

- Fixed compilation for native targets on non-x86 host systems (#336, #337).

### Added

- The `Delay` struct now offers direct `delay_us()` and `delay_ms()` methods
  without having to go through the embedded-hal traits (#344).

## [v0.7.2] - 2021-03-07

### Fixed

- Fixed a bug where calling `asm::delay()` with an argument of 0 or 1 would
  underflow, leading to a very long delay.

## [v0.7.1] - 2021-01-25

### Added

- New assembly methods `asm::semihosting_syscall`, `asm::bootstrap`, and
  `asm::bootload`.

### Deprecated

- `msp::write` has been deprecated in favor of `asm::bootstrap`. It was not
  possible to use `msp::write` without causing Undefined Behavior, so all
  existing users are encouraged to migrate.

### Fixed

- Fixed a bug in `asm::delay` which could lead to incorrect codegen and
  infinite loops.
- Improved timing guarantees of `asm::delay` on multiple-issue CPU cores.
- Additional compiler fences added to inline assembly where necessary.
- Fixed DWARF debug information in pre-built assembly binaries.

## [v0.7.0] - 2020-11-09

### Added

- New `InterruptNumber` trait is now required on interrupt arguments to the
  various NVIC functions, replacing the previous use of `Nr` from bare-metal.
  For backwards compatibility, `InterruptNumber` is implemented for types
  which are `Nr + Copy`, but this will be removed in a future version.
- Associated const `PTR` is introduced to Core Peripherals to
  eventually replace the existing `ptr()` API.
- A delay driver based on SysTick.
- You can now use LTO to inline assembly calls, even on stable Rust.
  See the `asm/lib.rs` documentation for more details.
- Initial ARMv8-M MPU support
- ICTR and ACTLR registers added
- Support for the Security Attribution Unit on ARMv8-M

### Changed

- Previously, asm calls without the `inline-asm` feature enabled used pre-built
  objects which were built by a GCC compiler, while `inline-asm` enabled the
  use of `llvm_asm!` calls. The asm system has been replaced with a new
  technique which generates Rust static libs for stable calling, and uses the
  new `asm!` macro with `inline-asm`. See the `asm/lib.rs` documentation for
  more details.
- Cache enabling now uses an assembly sequence to ensure correctness.
- `ptr()` methods are now `const`.

### Breaking Changes
- `SCB::invalidate_dcache` and related methods are now unsafe, see #188
- `Peripherals` struct is now non-exhaustive, so fields may be added in future
  non-breaking changes
- Removed `aligned` dependency
- Removed const-fn feature
- Removed previously deprecated APIs
    - `NVIC::clear_pending`
    - `NVIC::disable`
    - `NVIC::enable`
    - `NVIC::set_pending`
    - `SCB::system_reset`
- Removed `basepri`, `basepri_max`, and `faultmask` registers from thumbv8m.base

## [v0.6.7] - 2021-01-26

### Fixed

- Fixed missing `peripheral::itm` reexport.

## [v0.6.6] - 2021-01-26

### Fixed

- Fixed missing ITM reexport on `thumbv8m.base` targets.

## [v0.6.5] - 2021-01-24

### Changed

- This release is forwards-compatible with cortex-m 0.7, and depends on and
  re-exports many types from that version. Both 0.6.5 and 0.7 may co-exist
  in a build.

## [v0.6.4] - 2020-10-26

### Changed

- MSRV bumped to 1.36.0 due to `aligned` dependency.

### Fixed

- Drop AT&T syntax from inline asm, which was causing miscompilations with newer versions of the compiler.

## [v0.6.3] - 2020-07-20

### Added

- Initial Cortex-M Security Extension support for armv8m
- `UDF` intrinsic
- Methods to enable/disable exceptions in SCB

### Fixed

- Fix bug in `asm::delay` not updating status clobber flags
- Swapped to `llvm_asm!` to support inline assembly on new nightlies
- Our precompiled assembly routines have additional debug information
- ITM `is_fifo_ready` improved to support armv8
- Cache enabling moved to pre-built assembly routines to prevent possible
  undefined behaviour

## [v0.6.2] - 2020-01-12

### Added

- Allow writing to the `CONTROL` register via `register::control::write`
- Add `DWT::unlock()` for a safe way to unlock the DWT

### Deprecation

- Deprecated incorrectly included registers (`BASPRI`, `BASEPRI_MAX`, `FAULTMASK`) on `thumbv8.base`

## [v0.6.1] - 2019-08-21

### Fixed

- Better `Debug`, `PartialEq` and `Eq` for more types
- The `delay` function is fixed for Cortex-M0 MCUs

### Added

- Static version of `system_reset` as `system_reset2`
- Now uses `links = "cortex-m"` to not link multiple versions of the crate
- Masking of the NVIC is added `NVIC::{mask,unmask}`
- Now Rust 2018 edition
- `{M,P}SPLIM` access is now possible on ARMv8-M

### Deprecation

- `system_reset` is deprecated in favor of `sys_reset`

## [v0.6.0] - 2019-03-12

### Fixed

- Fix numerous registers which were incorrectly included for thumbv6
- `SHCRS` renamed to `SHCSR` in `SCB`

### Added

- Support for ARMv8-M (`thumbv8.base` and `thumbv8.main`)

- `SCB` gained methods to set and clear `SLEEPONEXIT` bit

- `NVIC` gained `STIR` register and methods to request an interrupt

- `DCB` gained methods to check if debugger is attached

## [v0.5.8] - 2018-10-27

### Added

- `SCB` gained methods to set, clear and check the pending state of the PendSV
  exception.

- `SCB` gained methods to set, clear and check the pending state of the SysTick
  exception.

- `SCB` gained methods to set and get the priority of system handlers like
  SVCall and SysTick.

- `NVIC` gained *static* methods, `pend` and `unpend`, to set and clear the
  pending state of interrupts.

### Changed

- The `NVIC.{clear,set}_pending` methods have been deprecated in favor of
  `NVIC::{unpend,pend}`.

## [v0.5.7] - 2018-09-06

### Added

- `DCB::enable_trace()` and `DCB::disable_trace()`

### Changed

- `iprintln!` no longer depends on `iprint!`. `cortex_m::iprintln!` will work
  even if `cortex_m::iprint` has not been imported.

## [v0.5.6] - 2018-08-27

### Fixed

- Removed duplicated symbols from binary blobs

- The check-blobs.sh script

## [v0.5.5] - 2018-08-27 - YANKED

### Changed

- This crate no longer depends on `arm-none-eabi-gcc`.

## [v0.5.4] - 2018-08-11

### Added

- A method to trigger a system reset. See `SCB.system_reset`.

### Fixed

- Made the VTOR register (see peripheral::SCB) available on `thumbv6m-none-eabi`. This register is
  present on Cortex-M0+, but not on Cortex-M0.

- Linking with LLD by marking all external assembly functions as `.thumb_func`. See
  https://bugs.llvm.org/show_bug.cgi?id=38435 for details.

## [v0.5.3] - 2018-08-02

### Fixed

- Don't assemble basepri*.s and faultmask.s for ARMv6-M. This fix the build when using `clang` as
  the assembler.

## [v0.5.2] - 2018-05-18

### Added

- `SCB` gained a pair of safe methods to set / clear the DEEPSLEEP bit.

- `asm::delay`, delay loops whose execution time doesn't depend on the optimization level.

## [v0.5.1] - 2018-05-13

### Added

- An opt-in `"const-fn"` feature that makes `Mutex.new` constructor into a `const fn`. This feature
  requires a nightly toolchain.

## [v0.5.0] - 2018-05-11

### Added

- `DebugMonitor` and `SecureFault` variants to the `Exception` enumeration.

- An optional `"inline-asm"` feature

### Changed

- [breaking-change] This crate now requires `arm-none-eabi-gcc` to be installed and available in
  `$PATH` when built with the `"inline-asm"` feature disabled (which is disabled by default).

- [breaking-change] The `register::{apsr,lr,pc}` modules are now behind the `"inline-asm"` feature.

- [breaking-change] Some variants of the `Exception` enumeration are no longer available on
  `thumbv6m-none-eabi`. See API docs for details.

- [breaking-change] Several of the variants of the `Exception` enumeration have been renamed to
  match the CMSIS specification.

- [breaking-change] fixed typo in `shcrs` field of `scb::RegisterBlock`; it was previously named
  `shpcrs`.

- [breaking-change] removed several fields from `scb::RegisterBlock` on ARMv6-M. These registers are
  not available on that sub-architecture.

- [breaking-change] changed the type of `scb::RegisterBlock.shpr` from `RW<u8>` to `RW<u32>` on
  ARMv6-M. These registers are word accessible only on that sub-architecture.

- [breaking-change] renamed the `mmar` field of `scb::RegisterBlock` to `mmfar` to match the CMSIS
  name.

- [breaking-change] removed the `iabr` field from `scb::RegisterBlock` on ARMv6-M. This register is
  not available on that sub-architecture.

- [breaking-change] removed several fields from `cpuid::RegisterBlock` on ARMv6-M. These registers
  are not available on that sub-architecture.

- [breaking-change] The `Mutex.new` constructor is not a `const fn` by default. To make it a `const
  fn` you have to opt into the `"const-fn"` feature, which was added in v0.5.1, and switch to a
  nightly compiler.

### Removed

- [breaking-change] The `exception` module has been removed. A replacement for `Exception::active`
  can be found in `SCB::vect_active`. A modified version `exception::Exception` can be found in the
  `peripheral::scb` module.

## [v0.4.3] - 2018-01-25

### Changed

- The initial value of a `singleton!` no longer needs to be evaluable in const context; it can now
  be a value computed at runtime, or even a capture of some other local variable.

## [v0.4.2] - 2018-01-17

### Fixed

- Added a missing `Send` implementation to all the peripherals.

## [v0.4.1] - 2018-01-16

### Changed

- `peripheral::Peripherals` is now re-exported at the root of the crate.

## [v0.4.0] - 2018-01-15

### Added

- Formatter and Flush Control register (FFCR) accessor to the TPIU register block.

- A `singleton!` macro that creates mutable reference to a statically allocated variable.

- A Cargo feature, `cm7-r0p1`, to work around a silicon erratum that affects writes to BASEPRI on
  Cortex-M7 r0p1 devices.

### Changed

- [breaking-change] All peripherals are now exposed as scoped singletons and they need to be `take`n
  into scope to become accessible.

- [breaking-change] The signatures of methods exposed by peripheral proxies have changed to
  better match the new scoped singletons semantics.

- All the thin wrappers around assembly instructions now panic when executed on non-ARM devices.

### Removed

- [breaking-change] APIs specific to ARMv7-M (`peripheral::{cbp, fpb, fpu, itm, tpiu}`, `itm`) when
  compiling for `thumb6m-none-eabi`.

## [v0.3.1] - 2017-07-20

### Changed

- `{basepri,basepri_max}::write` are now compiler barriers for the same reason
  that `interrupt::{disable,enable}` are: they are used to create critical
  sections.

## [v0.3.0] - 2017-07-07

### Changed

- [breaking-change] Renamed `StackedRergisters` to `ExceptionFrame` to better
  reflect the ARM documentation.

- [breaking-change] Renamed the variants of `Exception` to better match the
  ARM documentation.

- [breaking-change] Renamed `Exception::current` to `Exception::active` and
  changed the signature to return `None` when no exception is being serviced.

- Moved bits non specific to the Cortex-M architecture into the [`bare-metal`]
  crate with the goal of sharing code between this crate and crates tailored for
  other (microcontroller) architectures.

[`bare-metal`]: https://crates.io/crates/bare-metal

### Removed

- [breaking-change] The `ctxt` module along with the exception "tokens" in the
  `exception` module. The `cortex-m-rt` crate v0.3.0 provides a more ergonomic
  mechanism to add state to interrupts / exceptions; replace your uses of
  `Local` with that.

- [breaking-change] `default_handler`, `DEFAULT_HANDLERS` and `Handlers` from
  the `exception` module as well as `Reserved` from the root of the crate.
  `cortex-m-rt` v0.3.0 provides a mechanism to override exceptions and the
  default exception handler. Change your use of these `Handlers` and others to
  that.

### Fixed

- `interrupt::{enable,disable}` are now compiler barriers. The compiler should
  not reorder code around these function calls for memory safety; that is the
  case now.

## [v0.2.11] - 2017-06-16

### Added

- An API to maintain the different caches (DCache, ICache) on Cortex M7 devices.

### Fixed

- the definition of the `ehprint!` macro.
- the implementation of the FPU API.

## [v0.2.10] - 2017-06-05

### Added

- Functions for the instructions DMB, ISB and DSB

### Changed

- All the functions in the `asm` module are now `inline(always)`

## [v0.2.9] - 2017-05-30

### Fixed

- A bug in `itm::write_all` where it would ignore the length of the buffer and
  serialize contents that come after the buffer.

## [v0.2.8] - 2017-05-30 - YANKED

### Added

- An `itm::write_aligned` function to write 4 byte aligned buffers to an ITM
  port. This function is faster than `itm::write_all` for small buffers but
  requires the buffer to be aligned.

## [v0.2.7] - 2017-05-23

### Added

- `Dwt.enable_cycle_counter`

## [v0.2.6] - 2017-05-08

### Fixed

- [breaking-change]. MEMORY UNSAFETY. `Mutex` could be used as a channel to send
  interrupt tokens from one interrupt to other thus breaking the context `Local`
  abstraction. See reproduction case below. This has been fixed by making
  `Mutex` `Sync` only if the protected data is `Send`.

``` rust
#![feature(const_fn)]
#![feature(used)]
#![no_std]

use core::cell::RefCell;

use cortex_m::ctxt::Local;
use cortex_m::interrupt::Mutex;
use stm32f30x::interrupt::{self, Exti0, Exti1};

fn main() {
    // ..

    // trigger exti0
    // then trigger exti0 again
}

static CHANNEL: Mutex<RefCell<Option<Exti0>>> = Mutex::new(RefCell::new(None));
// Supposedly task *local* data
static LOCAL: Local<i32, Exti0> = Local::new(0);

extern "C" fn exti0(mut ctxt: Exti0) {
    static FIRST: Local<bool, Exti0> = Local::new(true);

    let first = *FIRST.borrow(&ctxt);

    // toggle
    if first {
        *FIRST.borrow_mut(&mut ctxt) = false;
    }

    if first {
        cortex_m::interrupt::free(
            |cs| {
                let channel = CHANNEL.borrow(cs);

                // BAD: transfer interrupt token to another interrupt
                *channel.borrow_mut() = Some(ctxt);
            },
        );

        return;
    }
    let _local = LOCAL.borrow_mut(&mut ctxt);

    // ..

    // trigger exti1 here

    // ..

    // `LOCAL` mutably borrowed up to this point
}

extern "C" fn exti1(_ctxt: Exti1) {
    cortex_m::interrupt::free(|cs| {
        let channel = CHANNEL.borrow(cs);
        let mut channel = channel.borrow_mut();

        if let Some(mut other_task) = channel.take() {
            // BAD: `exti1` has access to `exti0`'s interrupt token
            // so it can now mutably access local while `exti0` is also using it
            let _local = LOCAL.borrow_mut(&mut other_task);
        }
    });
}

#[allow(dead_code)]
#[used]
#[link_section = ".rodata.interrupts"]
static INTERRUPTS: interrupt::Handlers = interrupt::Handlers {
    Exti0: exti0,
    Exti1: exti1,
    ..interrupt::DEFAULT_HANDLERS
};
```

## [v0.2.5] - 2017-05-07 - YANKED

### Added

- Higher level API for the SysTick and FPU peripherals

### Fixed

- [breaking-change]. MEMORY UNSAFETY. `interrupt::enable` was safe to call
  inside an `interrupt::free` critical section thus breaking the preemption
  protection. The `interrupt::enable` method is now `unsafe`.

## [v0.2.4] - 2017-04-20 - YANKED

### Fixed

- [breaking-change]. MEMORY UNSAFETY. `interrupt::free` leaked the critical
  section making it possible to access a `Mutex` when interrupts are enabled
  (see below). This has been fixed by changing the signature of
  `interrupt::free`.

``` rust
static FOO: Mutex<bool> = Mutex::new(false);

fn main() {
    let cs = cortex_m::interrupt::free(|cs| cs);
    // interrupts are enabled at this point
    let foo = FOO.borrow(&cs);
}
```

## [v0.2.3] - 2017-04-11 - YANKED

### Fixed

- [breaking-change]. MEMORY UNSAFETY. Some concurrency models that use "partial"
  critical sections (cf. BASEPRI) can be broken by changing the priority of
  interrupts or by changing BASEPRI in some scenarios. For this reason
  `NVIC.set_priority` and `register::basepri::write` are now `unsafe`.

## [v0.2.2] - 2017-04-08 - YANKED

### Fixed

- [breaking-change]. MEMORY UNSAFETY. The `Mutex.borrow_mut` method has been
  removed as it can be used to bypass Rust's borrow checker and get, for
  example, two mutable references to the same data.

``` rust
static FOO: Mutex<bool> = Mutex::new(false);

fn main() {
    cortex_m::interrupt::free(|mut cs1| {
        cortex_m::interrupt::free(|mut cs2| {
            let foo: &mut bool = FOO.borrow_mut(&mut cs1);
            let and_foo: &mut bool = FOO.borrow_mut(&mut cs2);
        });
    });
}
```

## [v0.2.1] - 2017-03-12 - YANKED

### Changed

- The default exception handler now identifies the exception that's being
  serviced.

## [v0.2.0] - 2017-03-11 - YANKED

### Added

- Semihosting functionality in the `semihosting` module.

- `exception::Handlers` struct that represent the section of the vector table
  that contains the exception handlers.

- A default exception handler

- A high level API for the NVIC peripheral.

- Context local data.

- `borrow`/`borrow_mut` methods to `Mutex` that replace `lock`.

- API and macros to send bytes / (formatted) strings through ITM

### Changed

- [breaking-change] `StackFrame` has been renamed to `StackedRegisters` and
  moved into the `exceptions` module.

- [breaking-change] Core peripherals can now be modified via a `&-` reference
  and are no longer `Sync`.

- [breaking-change] `interrupt::free`'s closure now includes a critical section
  token, `CriticalSection`.

- [breaking-change] the core register API has been revamped for type safety.

- The safety of assembly wrappers like `wfi` and `interrupt::free` has been
  reviewed. In many cases, the functions are no longer unsafe.

- [breaking-change] `bkpt!` has been turned into a function. It no longer
  accepts an immediate value.

### Removed

- `vector_table` and its associated `struct`, `VectorTable`. It's not a good
  idea to give people a simple way to call the exception handlers.

- `Mutex`'s `lock` method as it's unsound. You could use it to get multiple
  `&mut -` references to the wrapped data.

## [v0.1.6] - 2017-01-22

### Added

- `Exception` a enumeration of the kind of exceptions the processor can service.
  There's also a `Exception::current` constructor that returns the `Exception`
  that's currently being serviced.

## [v0.1.5]

### Added

- `interrupt::Mutex`, a "mutex" based on critical sections.

### Changed

- The closure that `interrupt::free` takes can now return a value.

## [v0.1.4]

### Added

- `asm::nop`, a wrapper over the NOP instruction

## [v0.1.3]

### Added

- a StackFrame data structure

## [v0.1.2] - 2016-10-04

### Fixed

- Read/write Operations on registers (lr, cr, msp, etc.) which were reversed.

## [v0.1.1] - 2016-10-03 - YANKED

### Changed

- Small, non user visible change to make this crate compile further for $HOST (e.g. x86_64) with the
  goal of making it possible to test, on the HOST, downstream crates that depend on this one.

## v0.1.0 - 2016-09-27 - YANKED

### Added

- Functions to access core peripherals like NVIC, SCB and SysTick.
- Functions to access core registers like CONTROL, MSP and PSR.
- Functions to enable/disable interrupts
- Functions to get the vector table
- Wrappers over miscellaneous instructions like `bkpt`

[Unreleased]: https://github.com/rust-embedded/cortex-m/compare/v0.7.7...HEAD
[v0.7.7]: https://github.com/rust-embedded/cortex-m/compare/v0.7.6...v0.7.7
[v0.7.6]: https://github.com/rust-embedded/cortex-m/compare/v0.7.5...v0.7.6
[v0.7.5]: https://github.com/rust-embedded/cortex-m/compare/v0.7.4...v0.7.5
[v0.7.4]: https://github.com/rust-embedded/cortex-m/compare/v0.7.3...v0.7.4
[v0.7.3]: https://github.com/rust-embedded/cortex-m/compare/v0.7.2...v0.7.3
[v0.7.2]: https://github.com/rust-embedded/cortex-m/compare/v0.7.1...v0.7.2
[v0.7.1]: https://github.com/rust-embedded/cortex-m/compare/v0.7.0...v0.7.1
[v0.7.0]: https://github.com/rust-embedded/cortex-m/compare/v0.6.4...v0.7.0
[v0.6.7]: https://github.com/rust-embedded/cortex-m/compare/v0.6.6...v0.6.7
[v0.6.6]: https://github.com/rust-embedded/cortex-m/compare/v0.6.5...v0.6.6
[v0.6.5]: https://github.com/rust-embedded/cortex-m/compare/v0.6.4...v0.6.5
[v0.6.4]: https://github.com/rust-embedded/cortex-m/compare/v0.6.3...v0.6.4
[v0.6.3]: https://github.com/rust-embedded/cortex-m/compare/v0.6.2...v0.6.3
[v0.6.2]: https://github.com/rust-embedded/cortex-m/compare/v0.6.1...v0.6.2
[v0.6.1]: https://github.com/rust-embedded/cortex-m/compare/v0.6.0...v0.6.1
[v0.6.0]: https://github.com/rust-embedded/cortex-m/compare/v0.5.8...v0.6.0
[v0.5.8]: https://github.com/rust-embedded/cortex-m/compare/v0.5.7...v0.5.8
[v0.5.7]: https://github.com/rust-embedded/cortex-m/compare/v0.5.6...v0.5.7
[v0.5.6]: https://github.com/rust-embedded/cortex-m/compare/v0.5.5...v0.5.6
[v0.5.5]: https://github.com/rust-embedded/cortex-m/compare/v0.5.4...v0.5.5
[v0.5.4]: https://github.com/rust-embedded/cortex-m/compare/v0.5.3...v0.5.4
[v0.5.3]: https://github.com/rust-embedded/cortex-m/compare/v0.5.2...v0.5.3
[v0.5.2]: https://github.com/rust-embedded/cortex-m/compare/v0.5.1...v0.5.2
[v0.5.1]: https://github.com/rust-embedded/cortex-m/compare/v0.5.0...v0.5.1
[v0.5.0]: https://github.com/rust-embedded/cortex-m/compare/v0.4.3...v0.5.0
[v0.4.3]: https://github.com/rust-embedded/cortex-m/compare/v0.4.2...v0.4.3
[v0.4.2]: https://github.com/rust-embedded/cortex-m/compare/v0.4.1...v0.4.2
[v0.4.1]: https://github.com/rust-embedded/cortex-m/compare/v0.4.0...v0.4.1
[v0.4.0]: https://github.com/rust-embedded/cortex-m/compare/v0.3.1...v0.4.0
[v0.3.1]: https://github.com/rust-embedded/cortex-m/compare/v0.3.0...v0.3.1
[v0.3.0]: https://github.com/rust-embedded/cortex-m/compare/v0.2.11...v0.3.0
[v0.2.11]: https://github.com/rust-embedded/cortex-m/compare/v0.2.10...v0.2.11
[v0.2.10]: https://github.com/rust-embedded/cortex-m/compare/v0.2.9...v0.2.10
[v0.2.9]: https://github.com/rust-embedded/cortex-m/compare/v0.2.8...v0.2.9
[v0.2.8]: https://github.com/rust-embedded/cortex-m/compare/v0.2.7...v0.2.8
[v0.2.7]: https://github.com/rust-embedded/cortex-m/compare/v0.2.6...v0.2.7
[v0.2.6]: https://github.com/rust-embedded/cortex-m/compare/v0.2.5...v0.2.6
[v0.2.5]: https://github.com/rust-embedded/cortex-m/compare/v0.2.4...v0.2.5
[v0.2.4]: https://github.com/rust-embedded/cortex-m/compare/v0.2.3...v0.2.4
[v0.2.3]: https://github.com/rust-embedded/cortex-m/compare/v0.2.2...v0.2.3
[v0.2.2]: https://github.com/rust-embedded/cortex-m/compare/v0.2.1...v0.2.2
[v0.2.1]: https://github.com/rust-embedded/cortex-m/compare/v0.2.0...v0.2.1
[v0.2.0]: https://github.com/rust-embedded/cortex-m/compare/v0.1.6...v0.2.0
[v0.1.6]: https://github.com/rust-embedded/cortex-m/compare/v0.1.5...v0.1.6
[v0.1.5]: https://github.com/rust-embedded/cortex-m/compare/v0.1.4...v0.1.5
[v0.1.4]: https://github.com/rust-embedded/cortex-m/compare/v0.1.3...v0.1.4
[v0.1.3]: https://github.com/rust-embedded/cortex-m/compare/v0.1.2...v0.1.3
[v0.1.2]: https://github.com/rust-embedded/cortex-m/compare/v0.1.1...v0.1.2
[v0.1.1]: https://github.com/rust-embedded/cortex-m/compare/v0.1.0...v0.1.1
