extern crate rustc_version;

fn main() {
    let vers = rustc_version::version().unwrap();

    if vers.major == 1 && vers.minor < 31 {
        println!("cargo:rustc-cfg=unstable_const_fn")
    }
}
