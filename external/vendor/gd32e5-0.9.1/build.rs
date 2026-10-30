use std::env;
use std::fs;
use std::path::PathBuf;
fn main() {
    if env::var_os("CARGO_FEATURE_RT").is_some() {
        let out = &PathBuf::from(env::var_os("OUT_DIR").unwrap());
        println!("cargo:rustc-link-search={}", out.display());
        let device_file = if env::var_os("CARGO_FEATURE_GD32E503").is_some() {
            "src/gd32e503/device.x"
        } else if env::var_os("CARGO_FEATURE_GD32E505").is_some() {
            "src/gd32e505/device.x"
        } else if env::var_os("CARGO_FEATURE_GD32E507").is_some() {
            "src/gd32e507/device.x"
        } else if env::var_os("CARGO_FEATURE_GD32E508").is_some() {
            "src/gd32e508/device.x"
        } else { panic!("No device features selected"); };
        fs::copy(device_file, out.join("device.x")).unwrap();
        println!("cargo:rerun-if-changed={}", device_file);
    }
    println!("cargo:rerun-if-changed=build.rs");
}
