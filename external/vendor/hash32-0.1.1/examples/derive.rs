#[macro_use]
extern crate hash32_derive;
extern crate hash32;

use hash32::{FnvHasher, Hash, Hasher};

#[derive(Hash32)]
struct Led {
    state: bool,
}

#[derive(Hash32)]
struct Ipv4Addr([u8; 4]);

#[derive(Hash32)]
struct Generic<T> {
    inner: T,
}

fn main() {
    let mut fnv = FnvHasher::default();
    Led { state: true }.hash(&mut fnv);
    Generic { inner: 0 }.hash(&mut fnv);
    Ipv4Addr([127, 0, 0, 1]).hash(&mut fnv);
    println!("{}", fnv.finish())
}
