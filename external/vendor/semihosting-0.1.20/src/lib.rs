// SPDX-License-Identifier: Apache-2.0 OR MIT

/*!
<!-- Note: Document from sync-markdown-to-rustdoc:start through sync-markdown-to-rustdoc:end
     is synchronized from README.md. Any changes to that range are not preserved. -->
<!-- tidy:sync-markdown-to-rustdoc:start -->

Semihosting for AArch64, Arm, RISC-V, MIPS32, MIPS64, and Xtensa.

This library provides access to semihosting, a mechanism for programs running on the real or virtual (e.g., QEMU) target to communicate with I/O facilities on the host system. See the [Arm documentation](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst) for more information on semihosting.

APIs are categorized into the following four types:

- The top-level API (`semihosting::{io,fs,..}`) provides a subset of the standard library's similar APIs.
  - `io`: Provide no-std io traits and `std{in,out,err}`. (`std{in,out,err}` requires `stdio` feature, others are unconditionally provided)
  - `fs`: Provide methods to manipulate the contents of the host filesystem. (requires `fs` feature)
  - `process`: Provide `abort` and `exit`.
  - `dbg!`/`print{,ln}!`/`eprint{,ln}!`: macros to output to stdout/stderr. (requires `stdio` feature)

  Note that some APIs are not strictly a subset of the standard library.
  - API that uses types not available in `core` such as `Path` (technically, the same thing could be implemented, but it makes sense to use `CStr` directly, because when converting a long `Path`/`OsStr` to `CStr`, it needs to either [do an allocation](https://github.com/rust-lang/rust/blob/1.84.0/library/std/src/sys/pal/common/small_c_string.rs#L25-L26) or return an error)
  - API that panics on failure in `std` (in no-std it makes sense to return `Result` since `panic=abort` is default)

- Helpers that are useful when using this library.
  - `c!`: `CStr` literal macro. (Since Rust 1.77, this macro is soft-deprecated in favor of C string literals (`c"..."`).)

- `semihosting::sys` module, which provides low-level access to platform-specific semihosting interfaces.

- `semihosting::experimental` module, which provides experimental APIs. See [optional features](#optional-features) for more.

Additionally, this library provides a panic handler for semihosting, `-C panic=unwind` support, backtrace support, via [optional features](#optional-features).

## Platform Support

The following target architectures are supported:

| target_arch | Specification | `semihosting::sys` module | Note |
| ----------- | ------------- | ------------------------- | ---- |
| aarch64 | [Semihosting for AArch32 and AArch64](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst) | `sys::arm_compat` | |
| arm | [Semihosting for AArch32 and AArch64](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst) | `sys::arm_compat` | use `SVC` on A+R profile by default based on Arm's recommendation but it can be changed by [`trap-hlt` feature](#optional-features-trap-hlt). |
| riscv32/riscv64 | [RISC-V Semihosting](https://github.com/riscv-non-isa/riscv-semihosting/blob/1.0-rc2/riscv-semihosting.adoc) | `sys::arm_compat` | |
| xtensa | [OpenOCD Semihosting](https://github.com/espressif/openocd-esp32/blob/HEAD/src/target/espressif/esp_xtensa_semihosting.c) | `sys::arm_compat` | requires [`openocd-semihosting` feature](#optional-features-openocd-semihosting) |
| mips/mips32r6/mips64/mips64r6 | Unified Hosting Interface (MD01069) | `sys::mips` | |

The host must be running an emulator or a debugger attached to the target.

The following targets have been tested on CI. (qemu-system has been tested on Linux, macOS, and Windows hosts, and qemu-user on Linux host.)

| target                              | exit | all-apis \[1] (system) | all-apis \[1] (user-mode) | panic-unwind (system \[2]) | note |
| ----------------------------------- | ---- | ---------------------- | ------------------------- | -------------------------- | ---- |
| `aarch64-unknown-none{,-softfloat}` | ✓    | ✓                      | ✓                         | ✓                          |      |
| `{arm,thumb}v4t-none-eabi`          | ✓    |                        | ✓                         |                            |      |
| `{arm,thumb}v5te-none-eabi`         | ✓    | ✓                      | ✓                         |                            |      |
| `armv7a-none-eabi{,hf}`             | ✓    | ✓                      | ✓                         |                            |      |
| `armv7r-none-eabi{,hf}`             | ✓    | ✓                      | ✓                         |                            |      |
| `armebv7r-none-eabi{,hf}`           | ✓    |                        | ✓                         |                            |      |
| `armv8r-none-eabihf`                | ✓    | ✓                      | ✓                         |                            |      |
| `thumbv6m-none-eabi`                | ✓    | ✓                      | N/A                       |                            |      |
| `thumbv7m-none-eabi`                | ✓    | ✓                      | N/A                       |                            |      |
| `thumbv7em-none-eabi{,hf}`          | ✓    | ✓                      | N/A                       |                            |      |
| `thumbv8m.base-none-eabi`           | ✓    | ✓                      | N/A                       |                            |      |
| `thumbv8m.main-none-eabi{,hf}`      | ✓    | ✓                      | N/A                       |                            |      |
| `riscv32*-unknown-none-elf`         | ✓    | ✓                      | ✓                         | ✓                          |      |
| `riscv64*-unknown-none-elf`         | ✓    | ✓                      | ✓                         | ✓                          |      |
| `mips{,el}-unknown-none`            | ✓    | ✓                      | N/A                       |                            | \[3] \[4] |
| `mips64{,el}-unknown-none`          | ✓    | ✓                      | N/A                       |                            | \[3] \[4] |
| `mipsisa32r6{,el}-unknown-none`     | ✓    | ✓                      | N/A                       |                            | \[3] \[4] |
| `mipsisa64r6{,el}-unknown-none`     | ✓    | ✓                      | N/A                       |                            | \[3] \[4] |

\[1] `stdio`, `fs`, `time`, and `args`.<br>
\[2] I'm not sure how to test panic-unwind on qemu-user.<br>
\[3] Requires nightly due to `#![feature(asm_experimental_arch)]`.<br>
\[4] It seems [unsupported on QEMU 8.0+](https://qemu-project.gitlab.io/qemu/about/removed-features.html#mips-trap-and-emulate-kvm-support-removed-in-8-0).<br>

## Optional features

All features are disabled by default.

In general use cases, you probably only need the `stdio` feature that enables print-related macros and/or the `panic-handler` feature that exits with a non-zero error code on panic.

```toml
[dependencies]
semihosting = { version = "0.1", features = ["stdio", "panic-handler"] }
```

- **`alloc`**<br>
  Use `alloc`.

- **`stdio`**<br>
  Enable `semihosting::io::{stdin,stdout,stderr}` and `semihosting::{print*,eprint*,dbg}`.

- **`fs`**<br>
  Enable `semihosting::fs`.

- **`panic-handler`**<br>
  Provide panic handler based on `semihosting::process::exit`.

  If the `stdio` feature is also enabled, this attempt to output panic message and
  location to stderr.

- <a name="optional-features-trap-hlt"></a>**`trap-hlt`**<br>
  Arm-specific: Use HLT instruction on A+R profile.

  [Arm documentation](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#the-semihosting-interface) says:

  > The `HLT` encodings are new in version 2.0 of the semihosting specification.
  > Where possible, have semihosting callers continue to use the previously existing
  > trap instructions to ensure compatibility with legacy semihosting implementations.
  > These trap instructions are `HLT` for A64, `SVC` on A+R profile A32 or T32, and
  > `BKPT` on M profile. However, it is necessary to change from SVC to HLT instructions
  > to support AArch32 semihosting properly in a mixed AArch32/AArch64 system.
  >
  > ARM encourages semihosting callers to implement support for trapping using `HLT`
  > on A32 and T32 as a configurable option. ARM strongly discourages semihosting
  > callers from mixing the `HLT` and `SVC` mechanisms within the same executable.

  Based on the Arm's recommendation, this is implemented as an optional feature.

  Enabling this feature on architectures other than Arm A+R profile will result in a compile error.

- <a name="optional-features-openocd-semihosting"></a>**`openocd-semihosting`**<br>
  Xtensa-specific: Use OpenOCD Semihosting.

  Xtensa has two semihosting interfaces:

  - Tensilica ISS SIMCALL used in Cadence tools and [QEMU](https://www.qemu.org/docs/master/about/emulation.html#supported-targets).
  - Arm-semihosting-compatible semihosting interface used in [OpenOCD](https://github.com/espressif/openocd-esp32/blob/HEAD/src/target/espressif/esp_xtensa_semihosting.c) and [probe-rs](https://github.com/probe-rs/probe-rs/pull/2303). (This crate calls it "OpenOCD Semihosting", which is the same as the option name in [newlib-esp32](https://github.com/espressif/newlib-esp32/blob/esp-4.3.0_20240530/libgloss/xtensa/syscalls.c#L21).)

  This crate does not currently support SIMCALL-based semihosting, but users need to explicitly enable the feature to avoid accidentally selecting a different one than one actually want to use.

  Enabling this feature on architectures other than Xtensa will result in a compile error.

- **`portable-atomic`**<br>
  Use [portable-atomic]'s atomic types.

  portable-atomic provides atomic CAS on targets where the standard library does not provide atomic CAS.
  To use the `panic-unwind` feature on such targets (e.g., RISC-V without A-extension), you need to enable this feature.

  See [its documentation](https://github.com/taiki-e/portable-atomic#optional-features-critical-section) for details.

- **`args`**<br>
  Enable `semihosting::experimental::env::args`.

  Note:
  - This feature is experimental (tracking issue: [#1](https://github.com/taiki-e/semihosting/issues/1))
    and outside of the normal semver guarantees and minor or patch versions of semihosting may make
    breaking changes to them at any time.

- **`time`**<br>
  Enable `semihosting::experimental::time`.

  Note:
  - This feature is experimental (tracking issue: [#2](https://github.com/taiki-e/semihosting/issues/2))
    and outside of the normal semver guarantees and minor or patch versions of semihosting may make
    breaking changes to them at any time.

- **`panic-unwind`**<br>
  Provide `-C panic=unwind` support for panic handler and enable
  `semihosting::experimental::panic::catch_unwind`.

  This currently uses [unwinding] crate to support unwinding.
  See its documentation for supported platforms and requirements.

  Note:
  - This feature is experimental (tracking issue: [#3](https://github.com/taiki-e/semihosting/issues/3))
    and outside of the normal semver guarantees and minor or patch versions of semihosting may make
    breaking changes to them at any time.
  - This requires nightly compiler.
  - This implicitly enables the `alloc` and `panic-handler` features.
  - This uses atomic CAS. You need to use `portable-atomic` feature together if your target doesn't support atomic CAS (e.g., RISC-V without A-extension).
  - When enabling this feature, you may need to rebuild the standard library with
    `-C panic=unwind` for `catch_unwind` to work properly. The recommended way to
    rebuild the standard library is passing `-Z build-std="core,alloc"` option to cargo.

- **`backtrace`**<br>
  Provide backtrace support for panic handler.

  This currently uses [unwinding] crate to support backtrace.
  See its documentation for supported platforms and requirements.

  Note:
  - This feature is experimental (tracking issue: [#3](https://github.com/taiki-e/semihosting/issues/3))
    and outside of the normal semver guarantees and minor or patch versions of semihosting may make
    breaking changes to them at any time.
  - This requires nightly compiler.
  - This implicitly enables the `stdio` feature.
  - When enabling this, it is recommended to also enable the `panic-unwind` feature. Otherwise, a decent backtrace will not be displayed at this time. (Using [`-C force-unwind-tables`](https://doc.rust-lang.org/rustc/codegen-options/index.html#force-unwind-tables) may work, but has not been tested yet.)
  - Currently, the backtrace generated is not human-readable.

    ```text
    panicked at 'a', src/main.rs:86:13
    stack backtrace:
      0x84dc0
      0x8ed80
      0x8332c
      0x83654
      0x80644
      0x803cc
      0x809dc
      0x800bc
    ```

    You can use `addr2line` to resolve the addresses and [rustfilt] to demangle Rust symbols.
    For example, run the following command (please replace `<path/to/binary>` with your binary path), then paste the addresses:

    ```sh
    llvm-addr2line -fipe <path/to/binary> | rustfilt
    ```

[portable-atomic]: https://github.com/taiki-e/portable-atomic
[rustfilt]: https://github.com/luser/rustfilt
[unwinding]: https://github.com/nbdd0121/unwinding

<!-- tidy:sync-markdown-to-rustdoc:end -->
*/

#![no_std]
#![doc(test(
    no_crate_inject,
    attr(
        deny(warnings, rust_2018_idioms, single_use_lifetimes),
        allow(dead_code, unused_variables)
    )
))]
#![warn(unsafe_op_in_unsafe_fn)]
#![warn(
    // Lints that may help when writing public library.
    missing_debug_implementations,
    missing_docs,
    clippy::alloc_instead_of_core,
    clippy::exhaustive_enums,
    clippy::exhaustive_structs,
    clippy::impl_trait_in_params,
    // clippy::missing_inline_in_public_items,
    clippy::std_instead_of_alloc,
    clippy::std_instead_of_core,
)]
#![allow(
    clippy::inline_always,
    clippy::len_without_is_empty,
    clippy::missing_panics_doc,
    clippy::must_use_candidate,
    clippy::new_without_default
)]
#![cfg_attr(
    any(
        target_arch = "mips",
        target_arch = "mips32r6",
        target_arch = "mips64",
        target_arch = "mips64r6",
        target_arch = "xtensa",
    ),
    feature(asm_experimental_arch)
)]
// docs.rs only (cfg is enabled by docs.rs, not build script)
#![cfg_attr(docsrs, feature(doc_cfg))]

// 64-bit architecture's 32-bit ABI (e.g., AArch64 ILP32 ABI) are also
// unsupported yet (is there a semihosting interface defined for those ABIs?).
#[cfg(not(any(
    all(target_arch = "aarch64", target_pointer_width = "64"),
    target_arch = "arm",
    target_arch = "riscv32",
    all(target_arch = "riscv64", target_pointer_width = "64"),
    target_arch = "mips",
    target_arch = "mips32r6",
    all(target_arch = "mips64", target_pointer_width = "64"),
    all(target_arch = "mips64r6", target_pointer_width = "64"),
    target_arch = "xtensa",
)))]
compile_error!(
    "unsupported target; if you need support for this target, \
     please submit an issue at <https://github.com/taiki-e/semihosting>"
);
#[cfg(target_arch = "xtensa")]
#[cfg(not(feature = "openocd-semihosting"))]
compile_error!(
    "xtensa has two semihosting interfaces so you have to select implementation;\n\
    please enable `openocd-semihosting` feature if you want to use OpenOCD Semihosting used in OpenOCD, probe-rs, etc.\n\
    see <https://docs.rs/semihosting/latest/semihosting/#optional-features-openocd-semihosting> for more."
);
#[cfg(not(target_arch = "xtensa"))]
#[cfg(feature = "openocd-semihosting")]
compile_error!("`openocd-semihosting` feature is only available on Xtensa");
#[cfg(not(all(
    target_arch = "arm",
    not(any(target_feature = "mclass", semihosting_target_feature = "mclass")),
)))]
#[cfg(feature = "trap-hlt")]
compile_error!("`trap-hlt` feature is only available on Arm A+R profile");

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(doc)]
extern crate self as semihosting;
#[cfg(test)]
extern crate std;

#[cfg(feature = "panic-unwind")]
#[cfg(not(feature = "portable-atomic"))]
use core::sync::atomic;

#[cfg(feature = "panic-unwind")]
#[cfg(feature = "portable-atomic")]
use portable_atomic as atomic;

#[macro_use]
mod macros;

#[macro_use]
mod c_str;

#[macro_use]
pub mod fd;

#[macro_use]
pub mod io;

#[cfg(any(feature = "args", feature = "panic-unwind", feature = "time"))]
// Skip doc(cfg) due to rustdoc doesn't handle nested doc(cfg) well.
// #[cfg_attr(docsrs, doc(cfg(any(feature = "args", feature = "panic-unwind", feature = "time"))))]
pub mod experimental;
#[cfg(feature = "fs")]
#[cfg_attr(docsrs, doc(cfg(feature = "fs")))]
pub mod fs;
#[cfg(feature = "panic-handler")]
mod panicking;
pub mod process;
pub mod sys;

#[cfg(feature = "stdio")]
mod sealed {
    #[allow(unknown_lints, unnameable_types)] // Not public API. unnameable_types is available on Rust 1.79+
    pub trait Sealed {}
}

// This module provides core::ptr strict_provenance/exposed_provenance polyfill for pre-1.84 rustc.
#[allow(dead_code)]
mod ptr {
    #[cfg(not(semihosting_no_strict_provenance))]
    #[allow(unused_imports)]
    pub(crate) use core::ptr::{with_exposed_provenance, with_exposed_provenance_mut};

    #[cfg(semihosting_no_strict_provenance)]
    #[inline(always)]
    #[must_use]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub(crate) fn with_exposed_provenance<T>(addr: usize) -> *const T {
        addr as *const T
    }
    #[cfg(semihosting_no_strict_provenance)]
    #[inline(always)]
    #[must_use]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    pub(crate) fn with_exposed_provenance_mut<T>(addr: usize) -> *mut T {
        addr as *mut T
    }
}

// Not public API.
#[doc(hidden)]
pub mod __private {
    #[doc(hidden)]
    pub use core::{
        ffi::CStr,
        file, line,
        result::Result::{Err, Ok},
        stringify, write, writeln,
    };

    #[doc(hidden)]
    pub use crate::c_str::const_c_str_check;
}
