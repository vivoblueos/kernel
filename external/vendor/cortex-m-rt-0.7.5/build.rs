use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::{env, ffi::OsStr};

fn main() {
    let mut target = env::var("TARGET").unwrap();

    // When using a custom target JSON, `$TARGET` contains the path to that JSON file. By
    // convention, these files are named after the actual target triple, eg.
    // `thumbv7m-customos-elf.json`, so we extract the file stem here to allow custom target specs.
    let path = Path::new(&target);
    if path.extension() == Some(OsStr::new("json")) {
        target = path
            .file_stem()
            .map_or(target.clone(), |stem| stem.to_str().unwrap().to_string());
    }

    // Put the linker script somewhere the linker can find it
    let out = &PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let link_x = include_bytes!("link.x.in");
    let mut f = if env::var_os("CARGO_FEATURE_DEVICE").is_some() {
        let mut f = File::create(out.join("link.x")).unwrap();

        f.write_all(link_x).unwrap();

        // *IMPORTANT*: The weak aliases (i.e. `PROVIDED`) must come *after* `EXTERN(__INTERRUPTS)`.
        // Otherwise the linker will ignore user defined interrupts and always populate the table
        // with the weak aliases.
        writeln!(
            f,
            r#"
/* Provides weak aliases (cf. PROVIDED) for device specific interrupt handlers */
/* This will usually be provided by a device crate generated using svd2rust (see `device.x`) */
INCLUDE device.x"#
        )
        .unwrap();
        f
    } else {
        let mut f = File::create(out.join("link.x")).unwrap();
        f.write_all(link_x).unwrap();
        f
    };

    println!("cargo:rustc-check-cfg=cfg(armv6m)");
    println!("cargo:rustc-check-cfg=cfg(armv7m)");
    println!("cargo:rustc-check-cfg=cfg(armv8m)");
    println!("cargo:rustc-check-cfg=cfg(cortex_m)");
    println!("cargo:rustc-check-cfg=cfg(has_fpu)");

    let max_int_handlers = if target.starts_with("thumbv6m-") {
        println!("cargo:rustc-cfg=cortex_m");
        println!("cargo:rustc-cfg=armv6m");
        32
    } else if target.starts_with("thumbv7m-") || target.starts_with("thumbv7em-") {
        println!("cargo:rustc-cfg=cortex_m");
        println!("cargo:rustc-cfg=armv7m");
        240
    } else if target.starts_with("thumbv8m") {
        println!("cargo:rustc-cfg=cortex_m");
        println!("cargo:rustc-cfg=armv8m");
        496
    } else {
        // Non ARM target. We assume you're just testing the syntax.
        // This value seems as good as any.
        240
    };

    if target.ends_with("-eabihf") {
        println!("cargo:rustc-cfg=has_fpu");
    }

    // checking the size of the interrupts portion of the vector table is sub-architecture dependent
    writeln!(
        f,
        r#"
ASSERT(SIZEOF(.vector_table) <= 0x{:x}, "
There can't be more than {1} interrupt handlers. This may be a bug in
your device crate, or you may have registered more than {1} interrupt
handlers.");
"#,
        max_int_handlers * 4 + 0x40,
        max_int_handlers
    )
    .unwrap();

    println!("cargo:rustc-link-search={}", out.display());

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=link.x.in");
}
