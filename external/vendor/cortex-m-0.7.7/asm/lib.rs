//! FFI shim around the inline assembly in `inline.rs`.
//!
//! We use this file to precompile some assembly stubs into the static libraries you can find in
//! `bin`. Apps using the `cortex-m` crate then link against those static libraries and don't need
//! to build this file themselves.
//!
//! Nowadays the assembly stubs are no longer actual assembly files, but actually just this small
//! Rust crate that uses unstable inline assembly, coupled with the `xtask` tool to invoke rustc
//! and build the files.
//!
//! Precompiling this to a static lib allows users to call assembly routines from stable Rust, but
//! also perform [linker plugin LTO] with the precompiled artifacts to completely inline the
//! assembly routines into their code, which brings the "outline assembly" on par with "real" inline
//! assembly.
//!
//! For developers and contributors to `cortex-m`, this setup means that they don't have to install
//! any binutils, assembler, or C compiler to hack on the crate. All they need is to run `cargo
//! xtask assemble` to rebuild the archives from this file.
//!
//! Cool, right?
//!
//! # Rust version management
//!
//! Since inline assembly is still unstable, and we want to ensure that the created blobs are
//! up-to-date in CI, we have to pin the nightly version we use for this. The nightly toolchain is
//! stored in `asm-toolchain`.
//!
//! The `cargo xtask` automation will automatically install the `asm-toolchain` as well as all
//! Cortex-M targets needed to generate the blobs.
//!
//! [linker plugin LTO]: https://doc.rust-lang.org/stable/rustc/linker-plugin-lto.html

#![feature(asm)]
#![no_std]
#![crate_type = "staticlib"]
#![deny(warnings)]
// Don't warn about feature(asm) being stable on Rust >= 1.59.0
#![allow(stable_features)]

mod inline;

macro_rules! shims {
    (
        $( fn $name:ident( $($arg:ident: $argty:ty),* ) $(-> $ret:ty)?; )+
    ) => {
        $(
            #[no_mangle]
            pub unsafe extern "C" fn $name(
                $($arg: $argty),*
            ) $(-> $ret)? {
                crate::inline::$name($($arg),*)
            }
        )+
    };
}

shims! {
    fn __bkpt();
    fn __control_r() -> u32;
    fn __control_w(w: u32);
    fn __cpsid();
    fn __cpsie();
    fn __delay(cyc: u32);
    fn __dmb();
    fn __dsb();
    fn __isb();
    fn __msp_r() -> u32;
    fn __msp_w(val: u32);
    fn __nop();
    fn __primask_r() -> u32;
    fn __psp_r() -> u32;
    fn __psp_w(val: u32);
    fn __sev();
    fn __udf() -> !;
    fn __wfe();
    fn __wfi();
    fn __sh_syscall(nr: u32, arg: u32) -> u32;
    fn __bootstrap(msp: u32, rv: u32) -> !;
}

// v7m *AND* v8m.main, but *NOT* v8m.base
#[cfg(any(armv7m, armv8m_main))]
shims! {
    fn __basepri_max(val: u8);
    fn __basepri_r() -> u8;
    fn __basepri_w(val: u8);
    fn __faultmask_r() -> u32;
    fn __enable_icache();
    fn __enable_dcache();
}

#[cfg(armv7em)]
shims! {
    fn __basepri_max_cm7_r0p1(val: u8);
    fn __basepri_w_cm7_r0p1(val: u8);
}

// Baseline and Mainline.
#[cfg(armv8m)]
shims! {
    fn __tt(target: u32) -> u32;
    fn __ttt(target: u32) -> u32;
    fn __tta(target: u32) -> u32;
    fn __ttat(target: u32) -> u32;
    fn __msp_ns_r() -> u32;
    fn __msp_ns_w(val: u32);
    fn __bxns(val: u32);
}

// Mainline only.
#[cfg(armv8m_main)]
shims! {
    fn __msplim_r() -> u32;
    fn __msplim_w(val: u32);
    fn __psplim_r() -> u32;
    fn __psplim_w(val: u32);
}

// All targets with FPU.
#[cfg(has_fpu)]
shims! {
    fn __fpscr_r() -> u32;
    fn __fpscr_w(val: u32);
}

/// We *must* define a panic handler here, even though nothing here should ever be able to panic.
///
/// We prove that nothing will ever panic by calling a function that doesn't exist. If the panic
/// handler gets linked in, this causes a linker error. We always build this file with optimizations
/// enabled, but even without them the panic handler should never be linked in.
#[panic_handler]
#[link_section = ".text.asm_panic_handler"]
fn panic(_: &core::panic::PanicInfo) -> ! {
    extern "C" {
        #[link_name = "cortex-m internal error: panic handler not optimized out, please file an \
        issue at https://github.com/rust-embedded/cortex-m"]
        fn __cortex_m_should_not_panic() -> !;
    }

    unsafe {
        __cortex_m_should_not_panic();
    }
}
