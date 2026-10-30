rust-bitfield
=============

This crate provides macros to generate bitfield-like struct.

This a complete rewrite of the `bitfield` crate.
You can find the previous version in the [rust-bitfield-legacy](https://github.com/dzamlo/rust-bitfield-legacy) repository. This version works on the stable version of rustc and use a different syntax with different possibility.


## Example

An IPv4 header could be described like that:

```rust
bitfield!{
    /// A IPV4 header
    struct IpV4Header(MSB0 [u8]);
    u32;
    /// The version field
    get_version, _: 3, 0;
    /// The Internet Header Length (IHL) field
    get_ihl, _: 7, 4;
    /// ...
    get_dscp, _: 13, 8;
    get_ecn, _: 15, 14;
    get_total_length, _: 31, 16;
    get_identification, _: 47, 32;
    get_df, _: 49;
    get_mf, _: 50;
    get_fragment_offset, _: 63, 51;
    get_time_to_live, _: 71, 64;
    get_protocol, _: 79, 72;
    get_header_checksum, _: 95, 79;
    get_source_address, _: 127, 96;
    get_destination_address, _: 159, 128;
}
```

In this example, all the fields are read-only, the _ as setter name signals to skip the setter method.
The range at the end (e.g. 3, 0) defines the bit range where the information is encoded.

## Documentation

The documentation of the released version is available on [doc.rs](https://docs.rs/bitfield).

## Things to watch out for

### MSB and LSB ordering

When defining a field, the MSB comes first and the LSB second.

### Sign extension and valid range of signed field

When the type of a field is signed (`i8`, `i16`, ...) sign extension is done when reading the field. THis means that if the MSB of the read bits is 1, the returned values will be negative.

This also means that the valid range of value for the field is different that a unsigend field. A 4 bits field got from -8 (-2<sup>3</sup>) to 7 (2<sup>3</sup>-1) instead of 0 to 15.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
