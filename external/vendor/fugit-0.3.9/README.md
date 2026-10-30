# `fugit`

> `fugit` provides a comprehensive library of `Duration` and `Instant` for the handling of time in embedded systems, doing all it can at compile time.

This library is a heavily inspired of `std::chrono`'s `Duration` from C++ which does all it can at compile time.

## Aims

* `no_std` library with goals of user-friendliness and performance first
  * All methods are `const fn` that can be (i.e. non-trait methods)
  * Use no traits, concrete types all the way for maximum `const`-ification
  * Operations are supported between different bases and backing storages instead of implementing custom traits
  * All constants needed for comparing or changing timebase are guaranteed compile time generated
* Support for both `u32` and `u64` backing storage with efficient instruction lowering on MCUs
  * On Cortex-M3 and up: no soft-impls pulled in for both `u32` and `u64` except when changing base on `u64`
  * Comparisons on `u32` and `u64` do not use division, only changing base with all constants calculated at compile time
* Selection of base happens at compile time
  * A common problem is that run time changing of base robs us of a lot of optimization opportunities, but since there are no traits and short-hands select the correct base at compile time.

