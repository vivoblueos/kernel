use std::{env, path::PathBuf};

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let libs_dir = PathBuf::from(&manifest_dir).join("libs");

    let libs = [
        "btbb",
        "btdm_app",
        "coexist",
        "espnow",
        "mesh",
        "net80211",
        "core",
        "smartconfig",
        "wapi",
        "wpa_supplicant",
        "regulatory",
        "phy",
        "pp",
    ];

    println!(
        "cargo:rustc-link-search=native={}",
        libs_dir.canonicalize().unwrap().display()
    );
    for lib in libs {
        println!("cargo:rustc-link-lib={}", lib);
    }
}
