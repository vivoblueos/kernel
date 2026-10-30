use std::env;
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq)]
enum PolyfillLevel {
    // Native, ie no polyfill. Just reexport from core::sync::atomic
    Native,
    // Full polyfill: polyfill both load/store and CAS with critical sections
    Polyfill,
}

impl fmt::Display for PolyfillLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match *self {
            Self::Native => "native",
            Self::Polyfill => "polyfill",
        };
        write!(f, "{}", s)
    }
}

fn main() {
    let target = env::var("TARGET").unwrap();

    use PolyfillLevel::*;

    let patterns = [
        ("avr-*", (Polyfill, Polyfill)),
        ("msp430-none-elf", (Polyfill, Polyfill)),
        ("riscv32imac-*", (Native, Polyfill)),
        ("riscv32gc-*", (Native, Polyfill)),
        ("riscv32imc-*-espidf", (Native, Native)),
        ("riscv32*", (Polyfill, Polyfill)),
        ("thumbv4t-*", (Polyfill, Polyfill)),
        ("thumbv6m-*", (Polyfill, Polyfill)),
        ("thumbv7m-*", (Native, Polyfill)),
        ("thumbv7em-*", (Native, Polyfill)),
        ("thumbv8m.base-*", (Native, Polyfill)),
        ("thumbv8m.main-*", (Native, Polyfill)),
        ("xtensa-*-espidf", (Native, Native)),
        ("xtensa-esp32-*", (Native, Polyfill)),
        ("xtensa-esp32s2-*", (Polyfill, Polyfill)),
        ("xtensa-esp32s3-*", (Native, Polyfill)),
        ("xtensa-esp8266-*", (Polyfill, Polyfill)),
    ];

    if let Some((_, (level, level64))) = patterns
        .iter()
        .find(|(pattern, _)| matches(pattern, &target))
    {
        if *level == PolyfillLevel::Polyfill {
            println!("cargo:rustc-cfg=polyfill_u8");
            println!("cargo:rustc-cfg=polyfill_u16");
            println!("cargo:rustc-cfg=polyfill_u32");
            println!("cargo:rustc-cfg=polyfill_usize");
            println!("cargo:rustc-cfg=polyfill_i8");
            println!("cargo:rustc-cfg=polyfill_i16");
            println!("cargo:rustc-cfg=polyfill_i32");
            println!("cargo:rustc-cfg=polyfill_isize");
            println!("cargo:rustc-cfg=polyfill_ptr");
            println!("cargo:rustc-cfg=polyfill_bool");
        }

        if *level64 == PolyfillLevel::Polyfill {
            println!("cargo:rustc-cfg=polyfill_u64");
            println!("cargo:rustc-cfg=polyfill_i64");
        }
    } else {
        // If we don't know about the target, just reexport the entire `core::atomic::*`
        // This doesn't polyfill anything, but it's guaranteed to never fail build.
        println!("cargo:rustc-cfg=reexport_core");
    }
}

// tiny glob replacement to avoid pulling in more crates.
// Supports 0 or 1 wildcards `*`
fn matches(pattern: &str, val: &str) -> bool {
    if let Some(p) = pattern.find('*') {
        let prefix = &pattern[..p];
        let suffix = &pattern[p + 1..];
        val.len() >= prefix.len() + suffix.len() && val.starts_with(prefix) && val.ends_with(suffix)
    } else {
        val == pattern
    }
}
