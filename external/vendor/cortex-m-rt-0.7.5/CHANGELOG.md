# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

## [v0.7.5]

- Fix incorrect dependency on cortex-m-rt-macros in v0.7.4 which led to
  incorrect HardFault handlers being generated.
- MSRV is now Rust 1.61 to support syn verions >=2.0.68
- The `_stack_end` symbol is added, e.g. for use with MSPLIM (#565)
- Macros now expand to include an `unsafe` block and `allow(static_mut_refs)`
  when generating the `&'static mut` references in entry/interrupt handlers
  (#561, #558)
- `expect` attribute now permitted on entry/interrupt handlers (#557)
- Up to 496 interrupts now permitted on ARMv8-M (#555)
- Add new `paint-stack` feature which writes a fixed value to the entire stack
  during initialisation (#548)
- The hard fault handler `_HardFault` is now placed in the `.HardFault.user`
  linker section (#535)

## [v0.7.4]

- Add `zero-init-ram` feature to initialize RAM with zeros on startup.
  This can be necessary to properly initialise hardware error detection.
- Add optional `exception` argument for `HardFault`.
  It has one option `trampoline` which is `true` by default. When set to `false`,
  no trampoline will be created and the function will be called as the
  exception handler directly.
- MSRV increased to 1.60.0 to align with `embedded-hal` version 1.
- Improve linker error message when code does not fit into flash.
- Update documentation on using custom linker scripts and linker sections
  and on the `pre_init` function.

## [v0.7.3]

- Fixed a potential miscompilation caused by the initial stack pointer
  not being 8-byte aligned. This issue affected 0.7.1 and 0.7.2; for
  more details please see [the advisory] ([#467]).
- A linker error is generated if the initial stack pointer is not 8-byte aligned ([#464]).
- The initial stack pointer is now forced to be 8-byte aligned in the linker script,
  to defend against it being overridden outside of the cortex-m-rt linker script ([#465]).

[the advisory]: https://github.com/rust-embedded/cortex-m/discussions/469
[#464]: https://github.com/rust-embedded/cortex-m/issues/464
[#465]: https://github.com/rust-embedded/cortex-m/issues/465
[#467]: https://github.com/rust-embedded/cortex-m/issues/467

## [v0.7.2]

- MSRV is now Rust 1.59.
- Moved precompiled assembly blobs to `global_asm!`, requiring Rust 1.59.
- Add new `set_vtor` and `set-sp` features to conditionally set the VTOR and SP
  registers at device reset ([#423]).
- Allow (unstable) `naked` attribute on interrupt handlers and `pre_init`.

## Fixes

- Fix `cortex_m_rt::exception` macro no longer being usable fully-qualified ([#414])
- Fix veneer limit position in linker script ([#434]).

[#414]: https://github.com/rust-embedded/cortex-m/issues/414
[#423]: https://github.com/rust-embedded/cortex-m/issues/423
[#434]: https://github.com/rust-embedded/cortex-m/issues/434

## Notes

- From this release onwards, cortex-m-rt lives in the cortex-m repository;
  issue numbers refer there.

## [v0.7.1]

## Fixes

- Fix stack unwinding past `Reset` function ([#337])

[#337]: https://github.com/rust-embedded/cortex-m-rt/pull/337

## [v0.7.0]

### New Features

- Add support for CMSE secure gateway veneers ([#297]).
- Allow using the crate with custom target JSON specs ([#304]).
- Export Exception enum for other crates to use ([#224]).

[#224]: https://github.com/rust-embedded/cortex-m-rt/pull/224
[#297]: https://github.com/rust-embedded/cortex-m-rt/pull/297
[#304]: https://github.com/rust-embedded/cortex-m-rt/pull/304

### Fixes

- Various fixes to the linker script ([#265], [#286], [#287], [#323]).
- Use the correct ABI for the `main` symbol ([#278]).
- Add barriers after FPU enabling ([#279]).
- (ARMv6-M) Set LR value to a known value on reset ([#293]).
- Added CFI and size info to external assembly subroutines (`HardFaultTrampoline` and `FpuTrampoline`) ([#294]).
- Allow building the crate for macOS targets ([#306], [#310]).
- Perform RAM initialization in assembly, to avoid potential UB in Rust ([#301]).
- Perform volatile reads of ICSR in DefaultHandler ([#315]).

[#265]: https://github.com/rust-embedded/cortex-m-rt/pull/265
[#278]: https://github.com/rust-embedded/cortex-m-rt/pull/278
[#279]: https://github.com/rust-embedded/cortex-m-rt/pull/279
[#286]: https://github.com/rust-embedded/cortex-m-rt/pull/286
[#287]: https://github.com/rust-embedded/cortex-m-rt/pull/287
[#293]: https://github.com/rust-embedded/cortex-m-rt/pull/293
[#294]: https://github.com/rust-embedded/cortex-m-rt/pull/294
[#301]: https://github.com/rust-embedded/cortex-m-rt/pull/301
[#306]: https://github.com/rust-embedded/cortex-m-rt/pull/306
[#310]: https://github.com/rust-embedded/cortex-m-rt/pull/310
[#315]: https://github.com/rust-embedded/cortex-m-rt/pull/315
[#323]: https://github.com/rust-embedded/cortex-m-rt/pull/323

### Breaking Changes

- Make `ExceptionFrame`s fields private, adding setters and getters instead
  ([#239]).
- Only allow certain attributes on handlers, and apply them to the trampoline
  too ([#228]).
- Make it unsafe to define exception handlers for NMIs ([#289]).
- Check that exceptions exist on the target chip when registering a handler for
  them ([#308]).

[#239]: https://github.com/rust-embedded/cortex-m-rt/pull/239
[#228]: https://github.com/rust-embedded/cortex-m-rt/pull/228
[#289]: https://github.com/rust-embedded/cortex-m-rt/pull/289
[#308]: https://github.com/rust-embedded/cortex-m-rt/pull/308

### Other

- Change macros crate to use same version number as cortex-m-rt crate ([#245]).
- Discourage use of `pre_init` in documentation ([#248]).
- Backport: Use `links` in Cargo.toml to prevent multiple linking of
  cortex-m-rt ([#276]).

[#245]: https://github.com/rust-embedded/cortex-m-rt/pull/245
[#248]: https://github.com/rust-embedded/cortex-m-rt/pull/248
[#276]: https://github.com/rust-embedded/cortex-m-rt/pull/276

## Backport release: [v0.6.15] - 2021-07-12

### Fixed

- Backport: Mark .bss as NOLOAD ([#265])
- Backport: Fix possible overflow of .data region ([#286])
- Backport: Perform volatile reads of ICSR in DefaultHandler ([#315])

### Other
- Backport: Use `links` in Cargo.toml to prevent multiple linking of
  cortex-m-rt ([#276])
- Backport: Use same verison for macros crate as for cortex-m-rt itself
  ([#245])

[#245]: https://github.com/rust-embedded/cortex-m-rt/pull/245
[#265]: https://github.com/rust-embedded/cortex-m-rt/pull/265
[#276]: https://github.com/rust-embedded/cortex-m-rt/pull/276
[#286]: https://github.com/rust-embedded/cortex-m-rt/pull/286
[#315]: https://github.com/rust-embedded/cortex-m-rt/pull/315

## [v0.6.14] - 2021-05-19

### Fixed

- Backport: Allow building the crate for macOS targets ([#306], [#310]).

[#306]: https://github.com/rust-embedded/cortex-m-rt/issues/306
[#310]: https://github.com/rust-embedded/cortex-m-rt/issues/310

## Backport release: [v0.6.13] - 2020-09-07

### Fixed

- (ARMv6-M) Set LR value to a known value on reset (as the ARM spec requires)
- Added CFI and size info to external assembly subroutines (`HardFaultTrampoline`)

## Backport release: [v0.6.12] - 2020-01-26

### Fixed

- Fixed lint warnings getting emitted on macro-generated code.

## [v0.6.11] - 2019-12-04

### Changed

- Macros now generate a second trampoline function instead of randomizing the
  function's symbol name. This makes the build deterministic.
- [breaking-change] `static mut` resources no longer have `'static` lifetime
  except in the `#[entry]` function (this is a soundness fix; see [#212]).

[#212]: https://github.com/rust-embedded/cortex-m-rt/issues/212

## [v0.6.10] - 2019-07-25

### Fixed

- Linker template now takes and discard `*(.ARM.exidx)`

## [v0.6.9] - 2019-07-11

### Added

- Input `.uninit.*` sections are now collected into an output `.uninit` section.
  Uninitialized static variables are meant to be placed in these sections. The
  output `.uninit` section is not initialized by the runtime.

## [v0.6.8] - 2019-04-02

### Fixed

- Correct stack-pointer is selected on `HardFault`
- Linker template now takes and discard `*(.ARM.extab.*)`
- Misc. documentation fixes

### Changed

- Architecture added: `armv8-m.main`
- Cortex-M team added to `authors`
- The nightly build is allowed to fail in CI

## [v0.6.7] - 2018-12-15

### Fixed

- entry / exception / interrupt: `#[cfg]` attributes used on `static mut`
  variables are now properly handled.

## [v0.6.6] - 2018-12-06

### Changed

- Misuse of attributes now produce compiler errors with proper spans instead of
  panicking messages.

- The `HardFault` symbol has been renamed to `HardFaultTrampoline`; likewise the
  `UserHardFault` symbol has been renamed to `HardFault`. If you were using
  breakpoints on `UserHardFault` to detect hard fault you should now put those
  breakpoints on the `HardFault` symbol.

### Fixed

- Attributes on local `static mut` variables (declared at the beginning of
  `entry` / `interrupt` / `exception`) are now respected.

- The "GDB can now unwind HardFault callstacks" fix from the previous release
  broke `HardFault`'s' `&ExceptionFrame` argument (the pointer was off by 8
  bytes). This release fixes that problem without compromising GDB's ability to
  unwind `HardFault`s.

## [v0.6.5] - 2018-10-23

### Changed

- We now keep `.stack_sizes` by default, for use with external tooling.
- (macros) New `#[interrupt]` attribute added, similar to `#[exception]` for
  use with device-specific interrupt handlers.

### Fixed

- GDB can now unwind HardFault callstacks

## [v0.6.4] - 2018-09-25

### Changed

- (macros) Improved the error message when any of the attribute is used on the
  wrong kind of item.

### Fixed

- (macros) The expansion of the `exception` attribute now uses the `extern "C"`
  ABI which is what the hardware expects.

- (macros) `entry` and `exception` now respect the declared unsafety. That is
  `#[entry] unsafe main() -> !` won't require `unsafe` blocks to use `unsafe`
  API.

## [v0.6.3] - 2018-09-09

### Fixed

- Fixed the `rand` problem for real.

## [v0.6.2] - 2018-09-09

### Fixed

- Worked around a Cargo limitation that broke builds that depend on `rand`.

- Updated the documentation link in the README to point to working docs.

## [v0.6.1] - 2018-09-06

### Changed

- Produce a better error message if two (or more) copies of `cortex-m-rt` are
  going to be linked into a binary.

## [v0.6.0] - 2018-09-06

### Changed

- [breaking-change] the `entry!`, `pre_init!` and `exception!` macros have been
  replaced with attributes: `#[entry]`, `#[pre_init]` and `#[exception]`,
  respectively. This also changes the toolchain requirement to 1.30-beta or
  newer.

## [v0.5.3] - 2018-08-27

### Changed

- This crate no longer depends on `arm-none-eabi-gcc`.

## [v0.5.2] - 2018-08-11

### Added

* A `pre_init!` macro and related functionality to run a function immediately
  after reset, before memory initialisation

### Changed

- The `entry!` and `exception!` macros now also accept a closure instead of a path.

- `DefaultHandler` and `UserHardFault` now default to an infinite loop if left undefined.

### Fixed

* Linked script modified to correctly detect `FLASH` overflow caused by `.data`

## [v0.5.1] - 2018-05-14

### Fixed

- A recompilation problem where this `cortex-m-rt` would be recompiled every time `cargo build` is
  invoked.

## [v0.5.0] - 2018-05-12

### Added

- An `entry!` macro to set the entry point of the program.

- A `heap_start` function that returns a pointer into the start of the heap region.

- A `device` feature. When disabled this crate provides the interrupt vectors; when enabled the
  interrupt vectors are expected to be provided by another crate. Read the documentation for
  details.

### Changed

- This crate now compiles on the beta and stable channels.

- [breaking-change] this crate now requires `arm-none-eabi-gcc` to be installed and available in
  `$PATH` to compile.

- [breaking-change] the `start` lang item has been removed. The standard `main` interface won't
  work. Instead use `#![no_main]` and the `entry!` macro. See documentation for details.

- [breaking-change] the `default_handler!` macro has been merged into the `exception!` macro. Use
  `exception!(*, ..)` to set the default exception handler.

- [breaking-change] there's no weak default handler so a default handler must be defined by the
  application, or one of its dependencies.

- [breaking-change] the syntax of the third argument of the `exception!` handler has changed. See
  the documentation of the macro for details.

- [breaking-change] the exception names that the `exception!` macro accepts has changed to match the
  CMSIS specification. See the documentation of the macro for the list of names it accepts.

- [breaking-change] The number of symbol interfaces has been reduced. Check the advanced section of
  the documentation for details.

## [v0.4.0] - 2018-04-09

### Added

- LLD support. The linker script provided by this crate has been tweaked to support both LLD and GNU
  LD. To use LLD as a linker change `.cargo/config` to look like this:

``` diff
 [target.thumbv7m-none-eabi]
 rustflags = [
   "-C", "link-arg=-Tlink.x",
-  "-C", "linker=arm-none-eabi-ld",
-  "-Z", "linker-flavor=ld",
+  "-C", "linker=lld",
+  "-Z", "linker-flavor=ld.lld",
 ]
```

### Removed

- [breaking-change] Stack overflow protection has been removed. Unfortunately, supporting this
  feature produces totally wrong `arm-none-eabi-size` reports when LLD is used to link the
  program. If you need the stack overflow protection feature you can continue to use version
  v0.3.13+.

- [breaking-change] The "abort-on-panic" Cargo feature, which provided a `panic_fmt` implementation,
  has been removed. If you were using this feature you can instead use a [panic implementation
  crate][panic-impl].

[panic-impl]: https://crates.io/keywords/panic-impl

## [v0.3.15] - 2018-04-08

### Fixed

- Support the newest nightly

## [v0.3.14] - 2018-04-01

### Fixed

- `dev` channel support

## [v0.3.13] - 2018-02-17

### Added

- Fictitious `.stack` and `.heap` linker sections that represent the locations of the stack and the
  heap in RAM. You can visualize these linker sections by running `arm-none-eabi-size -Ax` over your
  binary.

- Zero cost stack overflow protection when you use the `cortex-m-rt-ld` linker. Check documentation
  for details.

- A `_heap_size` symbol that indicates how large the heap is. This symbol is only used when
  `cortex-m-rt-ld` is used as a linker.

## [v0.3.12] - 2018-01-17

### Fixed

- Support for recent nightlies.

## [v0.3.11] - 2018-01-17 - YANKED

### Changed

- Dynamically support recent nightlies, which have the `termination` lang item, and
  nightly-2017-09-22, which doesn't. That nightly version is used by the docs.rs builder. Supporting
  that version instead of rejecting it ensures this crate and its reverse-dependencies will get
  their documentation built by the docs.rs service.

## [v0.3.10] - 2018-01-17 - YANKED

### Removed

- The nightly date check from build script that improved error messages for users of old,
  unsupported nightlies. Unfortunately the check was preventing this crate and reverse-dependencies
  from getting their documentation build on docs.rs

## [v0.3.9] - 2018-01-07

### Fixed

- `cargo doc` warnings

## [v0.3.8] - 2017-12-29

### Added

- `Termination` lang item

### Changed

- The `start` lang item to match the new signature

## [v0.3.7] - 2017-12-23

### Added

- Support for overriding the DEBUG_MONITOR exception handler on ARMv7-M.

## [v0.3.6] - 2017-10-03

### Fixed

- Builds with multiple codegen units by forcing the linker to look harder for the exceptions vector
  table.

## [v0.3.5] - 2017-07-21

### Fixed

- Remove duplication of default exception handlers. This saves 32 bytes of Flash
  memory (.text).

## [v0.3.4] - 2017-07-19

### Changed

- Align the end of .rodata to a 4-byte boundary. With this the sections that
  will go into Flash memory will be 4 byte aligned at the start and at the
  end. Which seems to be required (?) by Cortex-M0 devices.

- .bss and .data are now padded so their sizes are multiple of 4 bytes. This
  improves the output of `objdump`; before, the output showed "Address
  0x20000004 is out of bounds".

- Linking now aborts if any of the input files contains a .got section. Dynamic
  relocations are not supported and Rust code is not relocatable by default.
  This error only occurs if C code that was compiled with the -fPIC flag is
  linked in. The error message will tell the user how to compile their C code
  without -fPIC.

## [v0.3.3] - 2017-07-14

### Changed

- Updated the documentation: it's no longer necessary to use the
  compiler-builtins repository since that crate landed in rust-lang/rust and
  it's now available in the `rust-src` component.

## [v0.3.2] - 2017-07-07

### Changed

- Tweaked documentation

## [v0.3.1] - 2017-07-07

### Fixed

- A warning when compiling for x86_64 and the "abort-on-panic" feature is
  enabled.

## [v0.3.0] - 2017-07-07

### Added

- A `default_handler!` macro to override the default exception handler.

- An `exception!` macro to override the handler for a particular exception.

### Changed

- The FPU will now be enabled before `main` if the target has FPU support.

- [breaking-change] the features "panic-over-itm" and "panic-over-semihosting"
  has been removed. the `panic_fmt` language item is now *not* included by
  default. An opt-in feature named "abort-on-panic" can be enabled to make this
  crate provide a `panic_fmt` implementation that simply aborts.

- [breaking-change] The sections `.rodata.{exceptions,interrupts}` have been
  renamed to `.vector_table.{exceptions,interrupts}`. This break the old
  mechanism for registering exceptions (`static EXCEPTIONS`); use the new ones:
  `default_handler!` and `exception!`.

- The `_stack_start` is now optional in the `memory.x` file. If unspecified its
  value will be set to `ORIGIN(RAM) + LENGTH(RAM)`.

## [v0.2.4] - 2017-06-03

### Added

- A non-allocatable `.stlog` section to support the [`stlog`] logging framework.

[`stlog`]: https://crates.io/crates/stlog

## [v0.2.3] - 2017-05-30

### Added

- A `_stext` symbol which can be specified in the linker script to customize the
  location of the `.text` section. If not specified the `.text` section will be
  placed right after the `.vector_table` section.

## [v0.2.2] - 2017-05-27

### Added

- A `_sheap` symbol where the heap can be located.

### Changed

- The linker sections have renamed / reorder to make `arm-none-eabi-size -A`
  more useful. You'll now see something like this:

```
$ arm-none-eabi-size -A hello
hello  :
section                size        addr
.vector_table          1024   134217728
.text                   288   134218752
.rodata                  14   134219040
```

- `cortex-m-rt::reset_handler` is now the entry point of all programs that link
  to `cortex-m-rt`. This makes GDB's `load` command work correctly. It will now
  set the Program Counter to `reset_handler` after flashing the program so
  there's no need to reset the microcontroller after flashing.

- Renamed `__exceptions` and `__interrupts` symbols, which are only used
  internally, to `_eexceptions` and `_einterrupts` respectively for consistency.

### Fixed

- Include input `.text` and `.rodata` sections (note: no suffix as in
  `.text.foo`) in the output file. (C) Code compiled without the equivalent
  `-ffunction-sections` / `-fdata-sections` may place stuff in those unsuffixed
  sections.

## [v0.2.1] - 2017-05-07

### Fixed

- Do not load the `.debug_gdb_script` section in flash. It's only needed for
  debugging.

## [v0.2.0] - 2017-04-27

### Changed

- [breaking-change] the `_stack_start` symbol is now required and must be
  provided in the `memory.x` file when using the "linker-script" feature. This
  symbol indicates where in memory the call stack will be allocated.

## [v0.1.3] - 2017-04-25

### Fixed

- A `rustdoc` warning

## [v0.1.2] - 2017-04-22

### Changed

- Unclutter the `reset_handler` function for a better debugging experience.

## [v0.1.1] - 2017-04-15

### Changed

- Improved linker error messages

## v0.1.0 - 2017-04-12

Initial release

[Unreleased]: https://github.com/rust-embedded/cortex-m/compare/c-m-rt-v0.7.5...HEAD
[v0.7.4]: https://github.com/rust-embedded/cortex-m/compare/c-m-rt-v0.7.4...c-m-rt-v0.7.5
[v0.7.4]: https://github.com/rust-embedded/cortex-m/compare/c-m-rt-v0.7.3...c-m-rt-v0.7.4
[v0.7.3]: https://github.com/rust-embedded/cortex-m/compare/c-m-rt-v0.7.2...c-m-rt-v0.7.3
[v0.7.2]: https://github.com/rust-embedded/cortex-m/compare/c-m-rt-v0.7.1...c-m-rt-v0.7.2
[v0.7.1]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.7.0...v0.7.1
[v0.7.0]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.11...v0.7.0
[v0.6.15]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.14...v0.6.15
[v0.6.14]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.13...v0.6.14
[v0.6.13]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.12...v0.6.13
[v0.6.12]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.11...v0.6.12
[v0.6.11]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.10...v0.6.11
[v0.6.10]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.9...v0.6.10
[v0.6.9]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.8...v0.6.9
[v0.6.8]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.7...v0.6.8
[v0.6.7]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.6...v0.6.7
[v0.6.6]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.5...v0.6.6
[v0.6.5]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.4...v0.6.5
[v0.6.4]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.3...v0.6.4
[v0.6.3]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.2...v0.6.3
[v0.6.2]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.1...v0.6.2
[v0.6.1]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.6.0...v0.6.1
[v0.6.0]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.5.3...v0.6.0
[v0.5.3]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.5.2...v0.5.3
[v0.5.2]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.5.1...v0.5.2
[v0.5.1]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.5.0...v0.5.1
[v0.5.0]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.4.0...v0.5.0
[v0.4.0]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.15...v0.4.0
[v0.3.15]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.14...v0.3.15
[v0.3.14]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.13...v0.3.14
[v0.3.13]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.12...v0.3.13
[v0.3.12]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.11...v0.3.12
[v0.3.11]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.10...v0.3.11
[v0.3.10]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.9...v0.3.10
[v0.3.9]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.8...v0.3.9
[v0.3.8]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.7...v0.3.8
[v0.3.7]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.6...v0.3.7
[v0.3.6]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.5...v0.3.6
[v0.3.5]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.4...v0.3.5
[v0.3.4]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.3...v0.3.4
[v0.3.3]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.2...v0.3.3
[v0.3.2]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.1...v0.3.2
[v0.3.1]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.3.0...v0.3.1
[v0.3.0]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.2.4...v0.3.0
[v0.2.4]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.2.3...v0.2.4
[v0.2.3]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.2.2...v0.2.3
[v0.2.2]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.2.1...v0.2.2
[v0.2.1]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.2.0...v0.2.1
[v0.2.0]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.1.3...v0.2.0
[v0.1.3]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.1.2...v0.1.3
[v0.1.2]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.1.1...v0.1.2
[v0.1.1]: https://github.com/rust-embedded/cortex-m-rt/compare/v0.1.0...v0.1.1
