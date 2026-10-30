//! Startup code and minimal runtime for Cortex-M microcontrollers
//!
//! This crate contains all the required parts to build a `no_std` application (binary crate) that
//! targets a Cortex-M microcontroller.
//!
//! # Features
//!
//! This crates takes care of:
//!
//! - The memory layout of the program. In particular, it populates the vector table so the device
//!   can boot correctly, and properly dispatch exceptions and interrupts.
//!
//! - Initializing `static` variables before the program entry point.
//!
//! - Enabling the FPU before the program entry point if the target is `-eabihf`.
//!
//! This crate also provides the following attributes:
//!
//! - [`#[entry]`][attr-entry] to declare the entry point of the program
//! - [`#[exception]`][attr-exception] to override an exception handler. If not overridden all
//!   exception handlers default to an infinite loop.
//!
//! This crate also implements a related attribute called `#[interrupt]`, which allows you
//! to define interrupt handlers. However, since which interrupts are available depends on the
//! microcontroller in use, this attribute should be re-exported and used from a peripheral
//! access crate (PAC).
//!
//! A [`#[pre_init]`][attr-pre_init] macro is also provided to run a function before RAM
//! initialisation, but its use is deprecated as it is not defined behaviour to execute Rust
//! code before initialisation. It is still possible to create a custom `pre_init` function
//! using assembly.
//!
//! The documentation for these attributes can be found in the [Attribute Macros](#attributes)
//! section.
//!
//! # Requirements
//!
//! ## `memory.x`
//!
//! This crate expects the user, or some other crate, to provide the memory layout of the target
//! device via a linker script named `memory.x`, described in this section.  The `memory.x` file is
//! used during linking by the `link.x` script provided by this crate. If you are using a custom
//! linker script, you do not need a `memory.x` file.
//!
//! ### `MEMORY`
//!
//! The linker script must specify the memory available in the device as, at least, two `MEMORY`
//! regions: one named `FLASH` and one named `RAM`. The `.text` and `.rodata` sections of the
//! program will be placed in the `FLASH` region, whereas the `.bss` and `.data` sections, as well
//! as the heap, will be placed in the `RAM` region.
//!
//! ```text
//! /* Linker script for the STM32F103C8T6 */
//! MEMORY
//! {
//!   FLASH : ORIGIN = 0x08000000, LENGTH = 64K
//!   RAM   : ORIGIN = 0x20000000, LENGTH = 20K
//! }
//! ```
//!
//! ### `_stack_start` / `_stack_end`
//!
//! The `_stack_start` optional symbol can be used to indicate where the call stack of the program
//! should be placed. If this symbol is not used then the stack will be placed at the *end* of the
//! `RAM` region -- the stack grows downwards towards smaller address. This is generally a sensible
//! default and most applications will not need to specify `_stack_start`. The same goes for
//! `_stack_end` which is automatically placed after the end of statically allocated RAM.
//!
//! **NOTE:** If you change `_stack_start`, make sure to also set `_stack_end` correctly to match
//! new stack area if you are using it, e.g for MSPLIM. The `_stack_end` is not used internally by
//! `cortex-m-rt` and is only for application use.
//!
//! For Cortex-M, the `_stack_start` must always be aligned to 8 bytes, which is enforced by
//! the linker script. If you override it, ensure that whatever value you set is a multiple
//! of 8 bytes. The `_stack_end` is aligned to 4 bytes.
//!
//! This symbol can be used to place the stack in a different memory region, for example:
//!
//! ```text
//! /* Linker script for the STM32F303VCT6 with stack in CCM */
//! MEMORY
//! {
//!     FLASH : ORIGIN = 0x08000000, LENGTH = 256K
//!
//!     /* .bss, .data and the heap go in this region */
//!     RAM   : ORIGIN = 0x20000000, LENGTH = 40K
//!
//!     /* Core coupled (faster) RAM dedicated to hold the stack */
//!     CCRAM : ORIGIN = 0x10000000, LENGTH = 8K
//! }
//!
//! _stack_start = ORIGIN(CCRAM) + LENGTH(CCRAM);
//! _stack_end = ORIGIN(CCRAM); /* Optional, add if used by the application */
//! ```
//!
//! ### `_stext`
//!
//! This optional symbol can be used to control where the `.text` section is placed. If omitted the
//! `.text` section will be placed right after the vector table, which is placed at the beginning of
//! `FLASH`. Some devices store settings like Flash configuration right after the vector table;
//! for these devices one must place the `.text` section after this configuration section --
//! `_stext` can be used for this purpose.
//!
//! ```text
//! MEMORY
//! {
//!   /* .. */
//! }
//!
//! /* The device stores Flash configuration in 0x400-0x40C so we place .text after that */
//! _stext = ORIGIN(FLASH) + 0x40C
//! ```
//!
//! # An example
//!
//! This section presents a minimal application built on top of `cortex-m-rt`. Apart from the
//! mandatory `memory.x` linker script describing the memory layout of the device, the hard fault
//! handler and the default exception handler must also be defined somewhere in the dependency
//! graph (see [`#[exception]`]). In this example we define them in the binary crate:
//!
//! ```no_run
//! #![no_main]
//! #![no_std]
//!
//! // Some panic handler needs to be included. This one halts the processor on panic.
//! use panic_halt as _;
//!
//! use cortex_m_rt::entry;
//!
//! // Use `main` as the entry point of this application, which may not return.
//! #[entry]
//! fn main() -> ! {
//!     // initialization
//!
//!     loop {
//!         // application logic
//!     }
//! }
//! ```
//!
//! To actually build this program you need to place a `memory.x` linker script somewhere the linker
//! can find it, e.g. in the current directory; and then link the program using `cortex-m-rt`'s
//! linker script: `link.x`. The required steps are shown below:
//!
//! ```text
//! $ cat > memory.x <<EOF
//! MEMORY
//! {
//!   FLASH : ORIGIN = 0x08000000, LENGTH = 64K
//!   RAM : ORIGIN = 0x20000000, LENGTH = 20K
//! }
//! EOF
//!
//! $ cargo rustc --target thumbv7m-none-eabi -- -C link-arg=-nostartfiles -C link-arg=-Tlink.x
//!
//! $ file target/thumbv7m-none-eabi/debug/app
//! app: ELF 32-bit LSB executable, ARM, EABI5 version 1 (SYSV), statically linked, (..)
//! ```
//!
//! # Optional features
//!
//! ## `device`
//!
//! If this feature is disabled then this crate populates the whole vector table. All the interrupts
//! in the vector table, even the ones unused by the target device, will be bound to the default
//! exception handler. This makes the final application device agnostic: you will be able to run it
//! on any Cortex-M device -- provided that you correctly specified its memory layout in `memory.x`
//! -- without hitting undefined behavior.
//!
//! If this feature is enabled then the interrupts section of the vector table is left unpopulated
//! and some other crate, or the user, will have to populate it. This mode is meant to be used in
//! conjunction with crates generated using `svd2rust`. Those peripheral access crates, or PACs,
//! will populate the missing part of the vector table when their `"rt"` feature is enabled.
//!
//! ## `set-sp`
//!
//! If this feature is enabled, the stack pointer (SP) is initialised in the reset handler to the
//! `_stack_start` value from the linker script. This is not usually required, but some debuggers
//! do not initialise SP when performing a soft reset, which can lead to stack corruption.
//!
//! ## `set-vtor`
//!
//! If this feature is enabled, the vector table offset register (VTOR) is initialised in the reset
//! handler to the start of the vector table defined in the linker script. This is not usually
//! required, but some bootloaders do not set VTOR before jumping to application code, leading to
//! your main function executing but interrupt handlers not being used.
//!
//! ## `zero-init-ram`
//!
//! If this feature is enabled, RAM is initialized with zeros during startup from the `_ram_start`
//! value to the `_ram_end` value from the linker script. This is not usually required, but might be
//! necessary to properly initialize memory integrity measures on some hardware.
//!
//! ## `paint-stack`
//!
//! Everywhere between `__sheap` and `_stack_start` is painted with the fixed value
//! `STACK_PAINT_VALUE`, which is `0xCCCC_CCCC`.
//! You can then inspect memory during debugging to determine how much of the stack has been used -
//! where the stack has been used the 'paint' will have been 'scrubbed off' and the memory will
//! have a value other than `STACK_PAINT_VALUE`.
//!
//! # Inspection
//!
//! This section covers how to inspect a binary that builds on top of `cortex-m-rt`.
//!
//! ## Sections (`size`)
//!
//! `cortex-m-rt` uses standard sections like `.text`, `.rodata`, `.bss` and `.data` as one would
//! expect. `cortex-m-rt` separates the vector table in its own section, named `.vector_table`. This
//! lets you distinguish how much space is taking the vector table in Flash vs how much is being
//! used by actual instructions (`.text`) and constants (`.rodata`).
//!
//! ```text
//! $ size -Ax target/thumbv7m-none-eabi/examples/app
//! target/thumbv7m-none-eabi/release/examples/app  :
//! section             size         addr
//! .vector_table      0x400    0x8000000
//! .text               0x88    0x8000400
//! .rodata              0x0    0x8000488
//! .data                0x0   0x20000000
//! .bss                 0x0   0x20000000
//! ```
//!
//! Without the `-A` argument `size` reports the sum of the sizes of `.text`, `.rodata` and
//! `.vector_table` under "text".
//!
//! ```text
//! $ size target/thumbv7m-none-eabi/examples/app
//!   text    data     bss     dec     hex filename
//!   1160       0       0    1660     67c target/thumbv7m-none-eabi/release/app
//! ```
//!
//! ## Symbols (`objdump`, `nm`)
//!
//! One will always find the following (unmangled) symbols in `cortex-m-rt` applications:
//!
//! - `Reset`. This is the reset handler. The microcontroller will execute this function upon
//!   booting. This function will call the user program entry point (cf. [`#[entry]`][attr-entry])
//!   using the `main` symbol so you will also find that symbol in your program.
//!
//! - `DefaultHandler`. This is the default handler. If not overridden using `#[exception] fn
//!   DefaultHandler(..` this will be an infinite loop.
//!
//! - `HardFault` and `_HardFault`. These function handle the hard fault handling and what they
//!   do depends on whether the hard fault is overridden and whether the trampoline is enabled (which it is by default).
//!   - No override: Both are the same function. The function is an infinite loop defined in the cortex-m-rt crate.
//!   - Trampoline enabled: `HardFault` is the real hard fault handler defined in assembly. This function is simply a
//!     trampoline that jumps into the rust defined `_HardFault` function. This second function jumps to the user-defined
//!     handler with the exception frame as parameter. This second jump is usually optimised away with inlining.
//!   - Trampoline disabled: `HardFault` is the user defined function. This means the user function is called directly
//!     from the vector table. `_HardFault` still exists, but is an empty function that is purely there for compiler
//!     diagnostics.
//!
//! - `__STACK_START`. This is the first entry in the `.vector_table` section. This symbol contains
//!   the initial value of the stack pointer; this is where the stack will be located -- the stack
//!   grows downwards towards smaller addresses.
//!
//! - `__RESET_VECTOR`. This is the reset vector, a pointer to the `Reset` function. This vector
//!   is located in the `.vector_table` section after `__STACK_START`.
//!
//! - `__EXCEPTIONS`. This is the core exceptions portion of the vector table; it's an array of 14
//!   exception vectors, which includes exceptions like `HardFault` and `SysTick`. This array is
//!   located after `__RESET_VECTOR` in the `.vector_table` section.
//!
//! - `__INTERRUPTS`. This is the device specific interrupt portion of the vector table; its exact
//!   size depends on the target device but if the `"device"` feature has not been enabled it will
//!   have a size of 32 vectors (on ARMv6-M), 240 vectors (on ARMv7-M) or 496 vectors (on ARMv8-M).
//!   This array is located after `__EXCEPTIONS` in the `.vector_table` section.
//!
//! - `__pre_init`. This is a function to be run before RAM is initialized. It defaults to an empty
//!   function. As this runs before RAM is initialised, it is not sound to use a Rust function for
//!   `pre_init`, and instead it should typically be written in assembly using `global_asm` or an
//!   external assembly file.
//!
//! If you override any exception handler you'll find it as an unmangled symbol, e.g. `SysTick` or
//! `SVCall`, in the output of `objdump`,
//!
//! # Advanced usage
//!
//! ## Custom linker script
//!
//! To use your own linker script, ensure it is placed in the linker search path (for example in
//! the crate root or in Cargo's `OUT_DIR`) and use it with `-C link-arg=-Tmy_script.ld` instead
//! of the normal `-C link-arg=-Tlink.x`. The provided `link.x` may be used as a starting point
//! for customisation.
//!
//! ## Setting the program entry point
//!
//! This section describes how [`#[entry]`][attr-entry] is implemented. This information is useful
//! to developers who want to provide an alternative to [`#[entry]`][attr-entry] that provides extra
//! guarantees.
//!
//! The `Reset` handler will call a symbol named `main` (unmangled) *after* initializing `.bss` and
//! `.data`, and enabling the FPU (if the target has an FPU). A function with the `entry` attribute
//! will be set to have the export name "`main`"; in addition, its mutable statics are turned into
//! safe mutable references (see [`#[entry]`][attr-entry] for details).
//!
//! The unmangled `main` symbol must have signature `extern "C" fn() -> !` or its invocation from
//! `Reset`  will result in undefined behavior.
//!
//! ## Incorporating device specific interrupts
//!
//! This section covers how an external crate can insert device specific interrupt handlers into the
//! vector table. Most users don't need to concern themselves with these details, but if you are
//! interested in how PACs generated using `svd2rust` integrate with `cortex-m-rt` read on.
//!
//! The information in this section applies when the `"device"` feature has been enabled.
//!
//! ### `__INTERRUPTS`
//!
//! The external crate must provide the interrupts portion of the vector table via a `static`
//! variable named`__INTERRUPTS` (unmangled) that must be placed in the `.vector_table.interrupts`
//! section of its object file.
//!
//! This `static` variable will be placed at `ORIGIN(FLASH) + 0x40`. This address corresponds to the
//! spot where IRQ0 (IRQ number 0) is located.
//!
//! To conform to the Cortex-M ABI `__INTERRUPTS` must be an array of function pointers; some spots
//! in this array may need to be set to 0 if they are marked as *reserved* in the data sheet /
//! reference manual. We recommend using a `union` to set the reserved spots to `0`; `None`
//! (`Option<fn()>`) may also work but it's not guaranteed that the `None` variant will *always* be
//! represented by the value `0`.
//!
//! Let's illustrate with an artificial example where a device only has two interrupt: `Foo`, with
//! IRQ number = 2, and `Bar`, with IRQ number = 4.
//!
//! ```no_run
//! pub union Vector {
//!     handler: unsafe extern "C" fn(),
//!     reserved: usize,
//! }
//!
//! extern "C" {
//!     fn Foo();
//!     fn Bar();
//! }
//!
//! #[link_section = ".vector_table.interrupts"]
//! #[no_mangle]
//! pub static __INTERRUPTS: [Vector; 5] = [
//!     // 0-1: Reserved
//!     Vector { reserved: 0 },
//!     Vector { reserved: 0 },
//!
//!     // 2: Foo
//!     Vector { handler: Foo },
//!
//!     // 3: Reserved
//!     Vector { reserved: 0 },
//!
//!     // 4: Bar
//!     Vector { handler: Bar },
//! ];
//! ```
//!
//! ### `device.x`
//!
//! Linking in `__INTERRUPTS` creates a bunch of undefined references. If the user doesn't set a
//! handler for *all* the device specific interrupts then linking will fail with `"undefined
//! reference"` errors.
//!
//! We want to provide a default handler for all the interrupts while still letting the user
//! individually override each interrupt handler. In C projects, this is usually accomplished using
//! weak aliases declared in external assembly files. We use a similar solution via the `PROVIDE`
//! command in the linker script: when the `"device"` feature is enabled, `cortex-m-rt`'s linker
//! script (`link.x`) includes a linker script named `device.x`, which must be provided by
//! whichever crate provides `__INTERRUPTS`.
//!
//! For our running example the `device.x` linker script looks like this:
//!
//! ```text
//! /* device.x */
//! PROVIDE(Foo = DefaultHandler);
//! PROVIDE(Bar = DefaultHandler);
//! ```
//!
//! This weakly aliases both `Foo` and `Bar`. `DefaultHandler` is the default exception handler and
//! that the core exceptions use unless overridden.
//!
//! Because this linker script is provided by a dependency of the final application the dependency
//! must contain a build script that puts `device.x` somewhere the linker can find. An example of
//! such build script is shown below:
//!
//! ```ignore
//! use std::env;
//! use std::fs::File;
//! use std::io::Write;
//! use std::path::PathBuf;
//!
//! fn main() {
//!     // Put the linker script somewhere the linker can find it
//!     let out = &PathBuf::from(env::var_os("OUT_DIR").unwrap());
//!     File::create(out.join("device.x"))
//!         .unwrap()
//!         .write_all(include_bytes!("device.x"))
//!         .unwrap();
//!     println!("cargo:rustc-link-search={}", out.display());
//! }
//! ```
//!
//! ## Uninitialized static variables
//!
//! The `.uninit` linker section can be used to leave `static mut` variables uninitialized. One use
//! case of unitialized static variables is to avoid zeroing large statically allocated buffers (say
//! to be used as thread stacks) -- this can considerably reduce initialization time on devices that
//! operate at low frequencies.
//!
//! The only correct way to use this section is with [`MaybeUninit`] types.
//!
//! [`MaybeUninit`]: https://doc.rust-lang.org/core/mem/union.MaybeUninit.html
//!
//! ```no_run,edition2018
//! # extern crate core;
//! use core::mem::MaybeUninit;
//!
//! const STACK_SIZE: usize = 8 * 1024;
//! const NTHREADS: usize = 4;
//!
//! #[link_section = ".uninit.STACKS"]
//! static mut STACKS: MaybeUninit<[[u8; STACK_SIZE]; NTHREADS]> = MaybeUninit::uninit();
//! ```
//!
//! Be very careful with the `link_section` attribute because it's easy to misuse in ways that cause
//! undefined behavior.
//!
//! ## Extra Sections
//!
//! Some microcontrollers provide additional memory regions beyond RAM and FLASH. For example,
//! some STM32 devices provide "CCM" or core-coupled RAM that is only accessible from the core. In
//! order to place variables in these sections using [`link_section`] attributes from your code,
//! you need to modify `memory.x` to declare the additional sections:
//!
//! [`link_section`]: https://doc.rust-lang.org/reference/abi.html#the-link_section-attribute
//!
//! ```text
//! MEMORY
//! {
//!     FLASH  (rx) : ORIGIN = 0x08000000, LENGTH = 1024K
//!     RAM    (rw) : ORIGIN = 0x20000000, LENGTH = 128K
//!     CCMRAM (rw) : ORIGIN = 0x10000000, LENGTH = 64K
//! }
//!
//! SECTIONS
//! {
//!     .ccmram (NOLOAD) : ALIGN(4)
//!     {
//!         *(.ccmram .ccmram.*);
//!         . = ALIGN(4);
//!     } > CCMRAM
//! }
//! ```
//!
//! You can then use something like this to place a variable into this specific section of memory:
//!
//! ```no_run,edition2018
//! # extern crate core;
//! # use core::mem::MaybeUninit;
//! #[link_section=".ccmram.BUFFERS"]
//! static mut BUF: MaybeUninit<[u8; 1024]> = MaybeUninit::uninit();
//! ```
//!
//! However, note that these sections are not initialised by cortex-m-rt, and so must be used
//! either with `MaybeUninit` types or you must otherwise arrange for them to be initialised
//! yourself, such as in `pre_init`.
//!
//! [attr-entry]: attr.entry.html
//! [attr-exception]: attr.exception.html
//! [attr-pre_init]: attr.pre_init.html
//!
//! # Minimum Supported Rust Version (MSRV)
//!
//! The MSRV of this release is Rust 1.61.0.

// # Developer notes
//
// - `link_section` is used to place symbols in specific places of the final binary. The names used
// here will appear in the linker script (`link.x`) in conjunction with the `KEEP` command.

#![deny(missing_docs)]
#![no_std]

extern crate cortex_m_rt_macros as macros;

/// The 32-bit value the stack is painted with before the program runs.
// Note: keep this value in-sync with the start-up assembly code, as we can't
// use const values in `global_asm!` yet.
#[cfg(feature = "paint-stack")]
pub const STACK_PAINT_VALUE: u32 = 0xcccc_cccc;

#[cfg(cortex_m)]
use core::arch::global_asm;
use core::fmt;

/// Parse cfg attributes inside a global_asm call.
#[cfg(cortex_m)]
macro_rules! cfg_global_asm {
    {@inner, [$($x:tt)*], } => {
        global_asm!{$($x)*}
    };
    (@inner, [$($x:tt)*], #[cfg($meta:meta)] $asm:literal, $($rest:tt)*) => {
        #[cfg($meta)]
        cfg_global_asm!{@inner, [$($x)* $asm,], $($rest)*}
        #[cfg(not($meta))]
        cfg_global_asm!{@inner, [$($x)*], $($rest)*}
    };
    {@inner, [$($x:tt)*], $asm:literal, $($rest:tt)*} => {
        cfg_global_asm!{@inner, [$($x)* $asm,], $($rest)*}
    };
    {$($asms:tt)*} => {
        cfg_global_asm!{@inner, [], $($asms)*}
    };
}

// This reset vector is the initial entry point after a system reset.
// Calls an optional user-provided __pre_init and then initialises RAM.
// If the target has an FPU, it is enabled.
// Finally jumps to the user main function.
#[cfg(cortex_m)]
cfg_global_asm! {
    ".cfi_sections .debug_frame
     .section .Reset, \"ax\"
     .global Reset
     .type Reset,%function
     .thumb_func",
    ".cfi_startproc
     Reset:",

    // If enabled, initialise the SP. This is normally initialised by the CPU itself or by a
    // bootloader, but some debuggers fail to set it when resetting the target, leading to
    // stack corruptions.
    #[cfg(feature = "set-sp")]
    "ldr r0, =_stack_start
     msr msp, r0",

    // If enabled, initialise VTOR to the start of the vector table. This is normally initialised
    // by a bootloader when the non-reset value is required, but some bootloaders do not set it,
    // leading to frustrating issues where everything seems to work but interrupts are never
    // handled. The VTOR register is optional on ARMv6-M, but when not present is RAZ,WI and
    // therefore safe to write to.
    #[cfg(feature = "set-vtor")]
    "ldr r0, =0xe000ed08
     ldr r1, =__vector_table
     str r1, [r0]",

    // Run user pre-init code which must be executed immediately after startup, before the
    // potentially time-consuming memory initialisation takes place.
    // Example use cases include disabling default watchdogs or enabling RAM.
    "bl __pre_init",

    // If enabled, initialize RAM with zeros. This is not usually required, but might be necessary
    // to properly initialize checksum-based memory integrity measures on safety-critical hardware.
    #[cfg(feature = "zero-init-ram")]
    "ldr r0, =_ram_start
     ldr r1, =_ram_end
     movs r2, #0
     0:
     cmp r1, r0
     beq 1f
     stm r0!, {{r2}}
     b 0b
     1:",

    // Initialise .bss memory. `__sbss` and `__ebss` come from the linker script.
    #[cfg(not(feature = "zero-init-ram"))]
    "ldr r0, =__sbss
     ldr r1, =__ebss
     movs r2, #0
     0:
     cmp r1, r0
     beq 1f
     stm r0!, {{r2}}
     b 0b
     1:",

    // If enabled, paint stack/heap RAM with 0xcccccccc.
    // `__sheap` and `_stack_start` come from the linker script.
    #[cfg(feature = "paint-stack")]
    "ldr r0, =__sheap
     ldr r1, =_stack_start
     ldr r2, =0xcccccccc // This must match STACK_PAINT_VALUE
     0:
     cmp r1, r0
     beq 1f
     stm r0!, {{r2}}
     b 0b
     1:",

    // Initialise .data memory. `__sdata`, `__sidata`, and `__edata` come from the linker script.
    "ldr r0, =__sdata
     ldr r1, =__edata
     ldr r2, =__sidata
     0:
     cmp r1, r0
     beq 1f
     ldm r2!, {{r3}}
     stm r0!, {{r3}}
     b 0b
     1:",

    // Potentially enable an FPU.
    // SCB.CPACR is 0xE000_ED88.
    // We enable access to CP10 and CP11 from priviliged and unprivileged mode.
    #[cfg(has_fpu)]
    "ldr r0, =0xE000ED88
     ldr r1, =(0b1111 << 20)
     ldr r2, [r0]
     orr r2, r2, r1
     str r2, [r0]
     dsb
     isb",

    // Jump to user main function.
    // `bl` is used for the extended range, but the user main function should not return,
    // so trap on any unexpected return.
    "bl main
     udf #0",

    ".cfi_endproc
     .size Reset, . - Reset",
}

/// Attribute to declare an interrupt (AKA device-specific exception) handler
///
/// **NOTE**: This attribute is exposed by `cortex-m-rt` only when the `device` feature is enabled.
/// However, that export is not meant to be used directly -- using it will result in a compilation
/// error. You should instead use the PAC (usually generated using `svd2rust`) re-export of
/// that attribute. You need to use the re-export to have the compiler check that the interrupt
/// exists on the target device.
///
/// # Syntax
///
/// ``` ignore
/// extern crate device;
///
/// // the attribute comes from the PAC not from cortex-m-rt
/// use device::interrupt;
///
/// #[interrupt]
/// fn USART1() {
///     // ..
/// }
/// ```
///
/// where the name of the function must be one of the device interrupts.
///
/// # Usage
///
/// `#[interrupt] fn Name(..` overrides the default handler for the interrupt with the given `Name`.
/// These handlers must have signature `[unsafe] fn() [-> !]`. It's possible to add state to these
/// handlers by declaring `static mut` variables at the beginning of the body of the function. These
/// variables will be safe to access from the function body.
///
/// If the interrupt handler has not been overridden it will be dispatched by the default exception
/// handler (`DefaultHandler`).
///
/// # Properties
///
/// Interrupts handlers can only be called by the hardware. Other parts of the program can't refer
/// to the interrupt handlers, much less invoke them as if they were functions.
///
/// `static mut` variables declared within an interrupt handler are safe to access and can be used
/// to preserve state across invocations of the handler. The compiler can't prove this is safe so
/// the attribute will help by making a transformation to the source code: for this reason a
/// variable like `static mut FOO: u32` will become `let FOO: &mut u32;`.
///
/// # Examples
///
/// - Using state within an interrupt handler
///
/// ``` ignore
/// extern crate device;
///
/// use device::interrupt;
///
/// #[interrupt]
/// fn TIM2() {
///     static mut COUNT: i32 = 0;
///
///     // `COUNT` is safe to access and has type `&mut i32`
///     *COUNT += 1;
///
///     println!("{}", COUNT);
/// }
/// ```
#[cfg(feature = "device")]
pub use macros::interrupt;

/// Attribute to declare the entry point of the program
///
/// The specified function will be called by the reset handler *after* RAM has been initialized. In
/// the case of the `thumbv7em-none-eabihf` target the FPU will also be enabled before the function
/// is called.
///
/// The type of the specified function must be `[unsafe] fn() -> !` (never ending function)
///
/// # Properties
///
/// The entry point will be called by the reset handler. The program can't reference to the entry
/// point, much less invoke it.
///
/// `static mut` variables declared within the entry point are safe to access. The compiler can't
/// prove this is safe so the attribute will help by making a transformation to the source code: for
/// this reason a variable like `static mut FOO: u32` will become `let FOO: &'static mut u32;`. Note
/// that `&'static mut` references have move semantics.
///
/// # Examples
///
/// - Simple entry point
///
/// ``` no_run
/// # #![no_main]
/// # use cortex_m_rt::entry;
/// #[entry]
/// fn main() -> ! {
///     loop {
///         /* .. */
///     }
/// }
/// ```
///
/// - `static mut` variables local to the entry point are safe to modify.
///
/// ``` no_run
/// # #![no_main]
/// # use cortex_m_rt::entry;
/// #[entry]
/// fn main() -> ! {
///     static mut FOO: u32 = 0;
///
///     let foo: &'static mut u32 = FOO;
///     assert_eq!(*foo, 0);
///     *foo = 1;
///     assert_eq!(*foo, 1);
///
///     loop {
///         /* .. */
///     }
/// }
/// ```
pub use macros::entry;

/// Attribute to declare an exception handler
///
/// # Syntax
///
/// ```
/// # use cortex_m_rt::exception;
/// #[exception]
/// fn SysTick() {
///     // ..
/// }
///
/// # fn main() {}
/// ```
///
/// where the name of the function must be one of:
///
/// - `DefaultHandler`
/// - `NonMaskableInt`
/// - `HardFault`
/// - `MemoryManagement` (a)
/// - `BusFault` (a)
/// - `UsageFault` (a)
/// - `SecureFault` (b)
/// - `SVCall`
/// - `DebugMonitor` (a)
/// - `PendSV`
/// - `SysTick`
///
/// (a) Not available on Cortex-M0 variants (`thumbv6m-none-eabi`)
///
/// (b) Only available on ARMv8-M
///
/// # Usage
///
/// ## HardFault handler
///
/// `#[exception(trampoline = true)] unsafe fn HardFault(..` sets the hard fault handler.
/// If the trampoline parameter is set to true, the handler must have signature `unsafe fn(&ExceptionFrame) -> !`.
/// If set to false, the handler must have signature `unsafe fn() -> !`.
///
/// This handler is not allowed to return as that can cause undefined behavior.
///
/// To maintain backwards compatibility the attribute can be used without trampoline parameter (`#[exception]`),
/// which sets the trampoline to true.
///
/// ## Default handler
///
/// `#[exception] unsafe fn DefaultHandler(..` sets the *default* handler. All exceptions which have
/// not been assigned a handler will be serviced by this handler. This handler must have signature
/// `unsafe fn(irqn: i16) [-> !]`. `irqn` is the IRQ number (See CMSIS); `irqn` will be a negative
/// number when the handler is servicing a core exception; `irqn` will be a positive number when the
/// handler is servicing a device specific exception (interrupt).
///
/// ## Other handlers
///
/// `#[exception] fn Name(..` overrides the default handler for the exception with the given `Name`.
/// These handlers must have signature `[unsafe] fn() [-> !]`. When overriding these other exception
/// it's possible to add state to them by declaring `static mut` variables at the beginning of the
/// body of the function. These variables will be safe to access from the function body.
///
/// # Properties
///
/// Exception handlers can only be called by the hardware. Other parts of the program can't refer to
/// the exception handlers, much less invoke them as if they were functions.
///
/// `static mut` variables declared within an exception handler are safe to access and can be used
/// to preserve state across invocations of the handler. The compiler can't prove this is safe so
/// the attribute will help by making a transformation to the source code: for this reason a
/// variable like `static mut FOO: u32` will become `let FOO: &mut u32;`.
///
/// # Safety
///
/// It is not generally safe to register handlers for non-maskable interrupts. On Cortex-M,
/// `HardFault` is non-maskable (at least in general), and there is an explicitly non-maskable
/// interrupt `NonMaskableInt`.
///
/// The reason for that is that non-maskable interrupts will preempt any currently running function,
/// even if that function executes within a critical section. Thus, if it was safe to define NMI
/// handlers, critical sections wouldn't work safely anymore.
///
/// This also means that defining a `DefaultHandler` must be unsafe, as that will catch
/// `NonMaskableInt` and `HardFault` if no handlers for those are defined.
///
/// The safety requirements on those handlers is as follows: The handler must not access any data
/// that is protected via a critical section and shared with other interrupts that may be preempted
/// by the NMI while holding the critical section. As long as this requirement is fulfilled, it is
/// safe to handle NMIs.
///
/// # Examples
///
/// - Setting the default handler
///
/// ```
/// use cortex_m_rt::exception;
///
/// #[exception]
/// unsafe fn DefaultHandler(irqn: i16) {
///     println!("IRQn = {}", irqn);
/// }
///
/// # fn main() {}
/// ```
///
/// - Overriding the `SysTick` handler
///
/// ```
/// use cortex_m_rt::exception;
///
/// #[exception]
/// fn SysTick() {
///     static mut COUNT: i32 = 0;
///
///     // `COUNT` is safe to access and has type `&mut i32`
///     *COUNT += 1;
///
///     println!("{}", COUNT);
/// }
///
/// # fn main() {}
/// ```
pub use macros::exception;

/// Attribute to mark which function will be called at the beginning of the reset handler.
///
/// **IMPORTANT**: This attribute can appear at most *once* in the dependency graph.
///
/// The function must have the signature of `unsafe fn()`.
///
/// # Safety
///
/// The function will be called before memory is initialized, as soon as possible after reset. Any
/// access of memory, including any static variables, will result in undefined behavior.
///
/// **Warning**: Due to [rvalue static promotion][rfc1414] static variables may be accessed whenever
/// taking a reference to a constant. This means that even trivial expressions such as `&1` in the
/// `#[pre_init]` function *or any code called by it* will cause **immediate undefined behavior**.
///
/// Users are advised to only use the `#[pre_init]` feature when absolutely necessary as these
/// constraints make safe usage difficult.
///
/// # Examples
///
/// ```
/// # use cortex_m_rt::pre_init;
/// #[pre_init]
/// unsafe fn before_main() {
///     // do something here
/// }
///
/// # fn main() {}
/// ```
///
/// [rfc1414]: https://github.com/rust-lang/rfcs/blob/master/text/1414-rvalue_static_promotion.md
pub use macros::pre_init;

// We export this static with an informative name so that if an application attempts to link
// two copies of cortex-m-rt together, linking will fail. We also declare a links key in
// Cargo.toml which is the more modern way to solve the same problem, but we have to keep
// __ONCE__ around to prevent linking with versions before the links key was added.
#[export_name = "error: cortex-m-rt appears more than once in the dependency graph"]
#[doc(hidden)]
pub static __ONCE__: () = ();

/// Registers stacked (pushed onto the stack) during an exception.
#[derive(Clone, Copy)]
#[repr(C)]
#[allow(dead_code)]
pub struct ExceptionFrame {
    r0: u32,
    r1: u32,
    r2: u32,
    r3: u32,
    r12: u32,
    lr: u32,
    pc: u32,
    xpsr: u32,
}

impl ExceptionFrame {
    /// Returns the value of (general purpose) register 0.
    #[inline(always)]
    pub fn r0(&self) -> u32 {
        self.r0
    }

    /// Returns the value of (general purpose) register 1.
    #[inline(always)]
    pub fn r1(&self) -> u32 {
        self.r1
    }

    /// Returns the value of (general purpose) register 2.
    #[inline(always)]
    pub fn r2(&self) -> u32 {
        self.r2
    }

    /// Returns the value of (general purpose) register 3.
    #[inline(always)]
    pub fn r3(&self) -> u32 {
        self.r3
    }

    /// Returns the value of (general purpose) register 12.
    #[inline(always)]
    pub fn r12(&self) -> u32 {
        self.r12
    }

    /// Returns the value of the Link Register.
    #[inline(always)]
    pub fn lr(&self) -> u32 {
        self.lr
    }

    /// Returns the value of the Program Counter.
    #[inline(always)]
    pub fn pc(&self) -> u32 {
        self.pc
    }

    /// Returns the value of the Program Status Register.
    #[inline(always)]
    pub fn xpsr(&self) -> u32 {
        self.xpsr
    }

    /// Sets the stacked value of (general purpose) register 0.
    ///
    /// # Safety
    ///
    /// This affects the `r0` register of the preempted code, which must not rely on it getting
    /// restored to its previous value.
    #[inline(always)]
    pub unsafe fn set_r0(&mut self, value: u32) {
        self.r0 = value;
    }

    /// Sets the stacked value of (general purpose) register 1.
    ///
    /// # Safety
    ///
    /// This affects the `r1` register of the preempted code, which must not rely on it getting
    /// restored to its previous value.
    #[inline(always)]
    pub unsafe fn set_r1(&mut self, value: u32) {
        self.r1 = value;
    }

    /// Sets the stacked value of (general purpose) register 2.
    ///
    /// # Safety
    ///
    /// This affects the `r2` register of the preempted code, which must not rely on it getting
    /// restored to its previous value.
    #[inline(always)]
    pub unsafe fn set_r2(&mut self, value: u32) {
        self.r2 = value;
    }

    /// Sets the stacked value of (general purpose) register 3.
    ///
    /// # Safety
    ///
    /// This affects the `r3` register of the preempted code, which must not rely on it getting
    /// restored to its previous value.
    #[inline(always)]
    pub unsafe fn set_r3(&mut self, value: u32) {
        self.r3 = value;
    }

    /// Sets the stacked value of (general purpose) register 12.
    ///
    /// # Safety
    ///
    /// This affects the `r12` register of the preempted code, which must not rely on it getting
    /// restored to its previous value.
    #[inline(always)]
    pub unsafe fn set_r12(&mut self, value: u32) {
        self.r12 = value;
    }

    /// Sets the stacked value of the Link Register.
    ///
    /// # Safety
    ///
    /// This affects the `lr` register of the preempted code, which must not rely on it getting
    /// restored to its previous value.
    #[inline(always)]
    pub unsafe fn set_lr(&mut self, value: u32) {
        self.lr = value;
    }

    /// Sets the stacked value of the Program Counter.
    ///
    /// # Safety
    ///
    /// This affects the `pc` register of the preempted code, which must not rely on it getting
    /// restored to its previous value.
    #[inline(always)]
    pub unsafe fn set_pc(&mut self, value: u32) {
        self.pc = value;
    }

    /// Sets the stacked value of the Program Status Register.
    ///
    /// # Safety
    ///
    /// This affects the `xPSR` registers (`IPSR`, `APSR`, and `EPSR`) of the preempted code, which
    /// must not rely on them getting restored to their previous value.
    #[inline(always)]
    pub unsafe fn set_xpsr(&mut self, value: u32) {
        self.xpsr = value;
    }
}

impl fmt::Debug for ExceptionFrame {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        struct Hex(u32);
        impl fmt::Debug for Hex {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "0x{:08x}", self.0)
            }
        }
        f.debug_struct("ExceptionFrame")
            .field("r0", &Hex(self.r0))
            .field("r1", &Hex(self.r1))
            .field("r2", &Hex(self.r2))
            .field("r3", &Hex(self.r3))
            .field("r12", &Hex(self.r12))
            .field("lr", &Hex(self.lr))
            .field("pc", &Hex(self.pc))
            .field("xpsr", &Hex(self.xpsr))
            .finish()
    }
}

/// Returns a pointer to the start of the heap
///
/// The returned pointer is guaranteed to be 4-byte aligned.
#[inline]
pub fn heap_start() -> *mut u32 {
    extern "C" {
        static mut __sheap: u32;
    }

    #[allow(unused_unsafe)] // no longer unsafe since rust 1.82.0
    unsafe {
        core::ptr::addr_of_mut!(__sheap)
    }
}

// Entry point is Reset.
#[doc(hidden)]
#[cfg_attr(cortex_m, link_section = ".vector_table.reset_vector")]
#[no_mangle]
pub static __RESET_VECTOR: unsafe extern "C" fn() -> ! = Reset;

#[doc(hidden)]
#[cfg_attr(cortex_m, link_section = ".HardFault.default")]
#[no_mangle]
pub unsafe extern "C" fn HardFault_() -> ! {
    #[allow(clippy::empty_loop)]
    loop {}
}

#[doc(hidden)]
#[no_mangle]
pub unsafe extern "C" fn DefaultHandler_() -> ! {
    #[allow(clippy::empty_loop)]
    loop {}
}

#[doc(hidden)]
#[no_mangle]
pub unsafe extern "C" fn DefaultPreInit() {}

/* Exceptions */
#[doc(hidden)]
pub enum Exception {
    NonMaskableInt,

    // Not overridable
    // HardFault,
    #[cfg(not(armv6m))]
    MemoryManagement,

    #[cfg(not(armv6m))]
    BusFault,

    #[cfg(not(armv6m))]
    UsageFault,

    #[cfg(armv8m)]
    SecureFault,

    SVCall,

    #[cfg(not(armv6m))]
    DebugMonitor,

    PendSV,

    SysTick,
}

#[doc(hidden)]
pub use self::Exception as exception;

extern "C" {
    fn Reset() -> !;

    fn NonMaskableInt();

    fn HardFault();

    #[cfg(not(armv6m))]
    fn MemoryManagement();

    #[cfg(not(armv6m))]
    fn BusFault();

    #[cfg(not(armv6m))]
    fn UsageFault();

    #[cfg(armv8m)]
    fn SecureFault();

    fn SVCall();

    #[cfg(not(armv6m))]
    fn DebugMonitor();

    fn PendSV();

    fn SysTick();
}

#[doc(hidden)]
#[repr(C)]
pub union Vector {
    handler: unsafe extern "C" fn(),
    reserved: usize,
}

#[doc(hidden)]
#[cfg_attr(cortex_m, link_section = ".vector_table.exceptions")]
#[no_mangle]
pub static __EXCEPTIONS: [Vector; 14] = [
    // Exception 2: Non Maskable Interrupt.
    Vector {
        handler: NonMaskableInt,
    },
    // Exception 3: Hard Fault Interrupt.
    Vector { handler: HardFault },
    // Exception 4: Memory Management Interrupt [not on Cortex-M0 variants].
    #[cfg(not(armv6m))]
    Vector {
        handler: MemoryManagement,
    },
    #[cfg(armv6m)]
    Vector { reserved: 0 },
    // Exception 5: Bus Fault Interrupt [not on Cortex-M0 variants].
    #[cfg(not(armv6m))]
    Vector { handler: BusFault },
    #[cfg(armv6m)]
    Vector { reserved: 0 },
    // Exception 6: Usage Fault Interrupt [not on Cortex-M0 variants].
    #[cfg(not(armv6m))]
    Vector {
        handler: UsageFault,
    },
    #[cfg(armv6m)]
    Vector { reserved: 0 },
    // Exception 7: Secure Fault Interrupt [only on Armv8-M].
    #[cfg(armv8m)]
    Vector {
        handler: SecureFault,
    },
    #[cfg(not(armv8m))]
    Vector { reserved: 0 },
    // 8-10: Reserved
    Vector { reserved: 0 },
    Vector { reserved: 0 },
    Vector { reserved: 0 },
    // Exception 11: SV Call Interrupt.
    Vector { handler: SVCall },
    // Exception 12: Debug Monitor Interrupt [not on Cortex-M0 variants].
    #[cfg(not(armv6m))]
    Vector {
        handler: DebugMonitor,
    },
    #[cfg(armv6m)]
    Vector { reserved: 0 },
    // 13: Reserved
    Vector { reserved: 0 },
    // Exception 14: Pend SV Interrupt [not on Cortex-M0 variants].
    Vector { handler: PendSV },
    // Exception 15: System Tick Interrupt.
    Vector { handler: SysTick },
];

// If we are not targeting a specific device we bind all the potential device specific interrupts
// to the default handler
#[cfg(all(any(not(feature = "device"), test), not(armv6m), not(armv8m)))]
#[doc(hidden)]
#[cfg_attr(cortex_m, link_section = ".vector_table.interrupts")]
#[no_mangle]
pub static __INTERRUPTS: [unsafe extern "C" fn(); 240] = [{
    extern "C" {
        fn DefaultHandler();
    }

    DefaultHandler
}; 240];

// ARMv8-M can have up to 496 device specific interrupts
#[cfg(all(not(feature = "device"), armv8m))]
#[doc(hidden)]
#[cfg_attr(cortex_m, link_section = ".vector_table.interrupts")]
#[no_mangle]
pub static __INTERRUPTS: [unsafe extern "C" fn(); 496] = [{
    extern "C" {
        fn DefaultHandler();
    }

    DefaultHandler
}; 496];

// ARMv6-M can only have a maximum of 32 device specific interrupts
#[cfg(all(not(feature = "device"), armv6m))]
#[doc(hidden)]
#[link_section = ".vector_table.interrupts"]
#[no_mangle]
pub static __INTERRUPTS: [unsafe extern "C" fn(); 32] = [{
    extern "C" {
        fn DefaultHandler();
    }

    DefaultHandler
}; 32];
