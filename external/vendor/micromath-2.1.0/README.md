# <img src="https://raw.githubusercontent.com/tarcieri/micromath/main/img/micromath.png" width="800">

[![Crate][crate-img]][crate-link]
[![Docs][docs-img]][docs-link]
[![Build Status][build-image]][build-link]
[![Safety Dance][safety-image]][safety-link]
![MSRV][msrv-image]
[![Apache 2.0/MIT Licensed][license-image]][license-link]

Embedded-friendly (i.e. `no_std`) Rust math library featuring fast, safe
floating point approximations for common arithmetic operations, trigonometry,
2D/3D vector types, statistical analysis, and quaternions.

Optimizes for performance and small code size at the cost of precision.

[Documentation][docs-link]

## Minimum Supported Rust Version

Requires Rust **1.47** or newer.

## SemVer Policy

We reserve the right to change the following in future releases with a minor
version bump *only*:

- MSRV
- `num-traits` version (optional dependency)

## Features

- [`f32` extension]:
  - Fast approximations:
    - [asin]
    - [acos]
    - [atan]
    - [atan2]
    - [cos]
    - [hypot]
    - [inv]
    - [invsqrt]
    - [ln]
    - [log]
    - [log2]
    - [log10]
    - [powf]
    - [exp]
    - [sin]
    - [sqrt]
    - [tan]
  - `std` polyfills:
    - [abs]
    - [ceil]
    - [floor]
    - [round]
    - [trunc]
    - [fract]
    - [copysign]
    - [signum]
    - [sin_cos]
    - [mul_add]
    - [recip]

- [Algebraic vector types]:
  - 2D:
    - [I8x2]
    - [I16x2]
    - [I32x2]
    - [U8x2]
    - [U16x2]
    - [U32x2]
    - [F32x2]
  - 3D:
    - [I8x3]
    - [I16x3]
    - [I32x3]
    - [U8x3]
    - [U16x3]
    - [U32x3]
    - [F32x3]
- [Statistical analysis]:
  - [mean]
  - [stddev]
  - [trim]
  - [variance]
- [Quaternions]

## Code of Conduct

We abide by the [Contributor Covenant][cc] and ask that you do as well.

For more information, please see [CODE_OF_CONDUCT.md].

## License

Copyright © 2019-2021 Tony Arcieri

Dual licensed under your choice of either of:

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

Incorporates portions of some tests from the [libm crate].
Copyright © 2018 Jorge Aparicio and also dual licensed under the
Apache 2.0 and MIT licenses. 

[//]: # (badges)

[crate-img]: https://img.shields.io/crates/v/micromath.svg?logo=rust
[crate-link]: https://crates.io/crates/micromath
[docs-img]: https://docs.rs/micromath/badge.svg
[docs-link]: https://docs.rs/micromath/
[build-image]: https://github.com/tarcieri/micromath/workflows/CI/badge.svg
[build-link]: https://github.com/tarcieri/micromath/actions
[safety-image]: https://img.shields.io/badge/unsafe-forbidden-success.svg
[safety-link]: https://github.com/rust-secure-code/safety-dance/
[msrv-image]: https://img.shields.io/badge/rustc-1.47+-blue.svg
[license-image]: https://img.shields.io/badge/license-Apache2.0/MIT-blue.svg
[license-link]: https://github.com/tarcieri/micromath/blob/main/LICENSE-APACHE

[//]: # (general links)

[`f32` extension]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html
[asin]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.asin
[acos]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.acos
[atan]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.atan
[atan2]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.atan2
[cos]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.cos
[hypot]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.hypot
[inv]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.inv
[invsqrt]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.invsqrt
[ln]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.ln
[log]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.log
[log2]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.log2
[log10]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.log10
[powf]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.powf
[powi]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.powi
[exp]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.exp
[sin]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.sin
[sqrt]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.sqrt
[tan]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.tan
[abs]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.abs
[ceil]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.ceil
[floor]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.floor
[round]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.round
[trunc]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.trunc
[fract]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.fract
[copysign]: https://docs.rs/micromath/latest/micromath/trait.F32Ext.html#tymethod.copysign
[Algebraic vector types]: https://docs.rs/micromath/latest/micromath/vector/index.html
[I8x2]: https://docs.rs/micromath/latest/micromath/vector/struct.I8x2.html
[I16x2]: https://docs.rs/micromath/latest/micromath/vector/struct.I16x2.html
[I32x2]: https://docs.rs/micromath/latest/micromath/vector/struct.I32x2.html
[U8x2]: https://docs.rs/micromath/latest/micromath/vector/struct.U8x2.html
[U16x2]: https://docs.rs/micromath/latest/micromath/vector/struct.U16x2.html
[U32x2]: https://docs.rs/micromath/latest/micromath/vector/struct.U32x2.html
[F32x2]: https://docs.rs/micromath/latest/micromath/vector/struct.F32x2.html
[I8x3]: https://docs.rs/micromath/latest/micromath/vector/struct.I8x3.html
[I16x3]: https://docs.rs/micromath/latest/micromath/vector/struct.I16x3.html
[I32x3]: https://docs.rs/micromath/latest/micromath/vector/struct.I32x3.html
[U8x3]: https://docs.rs/micromath/latest/micromath/vector/struct.U8x3.html
[U16x3]: https://docs.rs/micromath/latest/micromath/vector/struct.U16x3.html
[U32x3]: https://docs.rs/micromath/latest/micromath/vector/struct.U32x3.html
[F32x3]: https://docs.rs/micromath/latest/micromath/vector/struct.F32x3.html
[Statistical analysis]: https://docs.rs/micromath/latest/micromath/statistics/index.html
[mean]: https://docs.rs/micromath/latest/micromath/statistics/trait.Mean.html
[stddev]: https://docs.rs/micromath/latest/micromath/statistics/trait.StdDev.html
[trim]: https://docs.rs/micromath/latest/micromath/statistics/trim/trait.Trim.html
[variance]: https://docs.rs/micromath/latest/micromath/statistics/trait.Variance.html
[Quaternions]: https://docs.rs/micromath/latest/micromath/quaternion/struct.Quaternion.html
[libm crate]: https://github.com/rust-lang-nursery/libm
[vek crate]: https://github.com/yoanlcq/vek
[approx crate]: https://crates.io/crates/approx
[cc]: https://contributor-covenant.org
[CODE_OF_CONDUCT.md]: https://github.com/tarcieri/micromath/blob/main/CODE_OF_CONDUCT.md
