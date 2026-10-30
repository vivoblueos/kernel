# `flat_device_tree`

**NOTE** Friendly fork of [`fdt`](https://github.com/repnop/fdt).

A pure-Rust `#![no_std]` crate for parsing Flattened Devicetrees, with the goal of having a
very ergonomic and idiomatic API.

[![crates.io](https://img.shields.io/crates/v/flat_device_tree.svg)](https://crates.io/crates/flat_device_tree) [![Documentation](https://docs.rs/flat_device_tree/badge.svg)](https://docs.rs/flat_device_tree) [![Build](https://ci.codeberg.org/api/badges/13272/status.svg)](https://ci.codeberg.org/repos/13272)

## License

This crate is licensed under the Mozilla Public License 2.0 (see the LICENSE file).

## Example

```rust
static MY_FDT: &[u8] = include_bytes!("../dtb/test.dtb");

fn main() {
    let fdt = fdt::Fdt::new(MY_FDT).unwrap();

    println!("This is a devicetree representation of a {}", fdt.root().model());
    println!("...which is compatible with at least: {}", fdt.root().compatible().first());
    println!("...and has {} CPU(s)", fdt.cpus().count());
    println!(
        "...and has at least one memory location at: {:#X}\n",
        fdt.memory().regions().next().unwrap().starting_address as usize
    );

    let chosen = fdt.chosen();
    if let Some(bootargs) = chosen.bootargs() {
        println!("The bootargs are: {:?}", bootargs);
    }

    if let Some(stdout) = chosen.stdout() {
        println!("It would write stdout to: {}", stdout.node().name);
    }

    let soc = fdt.find_node("/soc");
    println!("Does it have a `/soc` node? {}", if soc.is_some() { "yes" } else { "no" });
    if let Some(soc) = soc {
        println!("...and it has the following children:");
        for child in soc.children() {
            println!("    {}", child.name);
        }
    }
}
```
