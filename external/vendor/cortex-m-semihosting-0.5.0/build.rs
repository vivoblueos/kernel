use std::env;

fn main() {
    let target = env::var("TARGET").unwrap();

    if target.starts_with("thumbv") {
        println!("cargo:rustc-cfg=thumb");
    }
}
