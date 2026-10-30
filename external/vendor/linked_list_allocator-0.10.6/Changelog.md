# Unreleased

# 0.10.6 – 2026-04-14

- Fix potential panic due to huge layout ([#79](https://github.com/rust-osdev/linked-list-allocator/pull/79))
- Fix `alloc_ref` build on recent nightly by using renamed `NonNull::dangling` ([#90](https://github.com/rust-osdev/linked-list-allocator/pull/90))

## Internal

- Fix warnings about `cfg(fuzzing)` ([#82](https://github.com/rust-osdev/linked-list-allocator/pull/82))
- Remove stabilized miri flags and feature ([#81](https://github.com/rust-osdev/linked-list-allocator/pull/81))
- Remove potential undefined behavior in fuzz chaos harness ([#80](https://github.com/rust-osdev/linked-list-allocator/pull/80))
- Upgrade plain-HTTP links to HTTPS in Cargo.toml ([#78](https://github.com/rust-osdev/linked-list-allocator/pull/78))

# 0.10.5 – 2023-03-04

- Remove features `const_mut_refs` and `use_spin_nightly`.

  Since rust 1.61, the [required const features](https://github.com/rust-lang/rust/pull/93827) are available in stable rust, and `lock_api` >= 0.4.7 automatically uses them.
  To avoid a breaking change, the features are still listed in Cargo.toml, but have no effect and are marked as deprecated.
  This bumps the minimum supported rust version to 1.61.

# 0.10.4 – 2022-10-10

- Fix [memory leak of small back paddings](https://github.com/rust-osdev/linked-list-allocator/issues/66) by considering regions that would result in such small back paddings as unsuitable ([#71](https://github.com/rust-osdev/linked-list-allocator/pull/71))

# 0.10.3 – 2022-09-06

- Fix build on stable by adding missing field in `HoleList` initializer ([#68](https://github.com/rust-osdev/linked-list-allocator/pull/68))
  - Fixes a bug introduced in `v0.10.2`.

# 0.10.2 – 2022-09-06

Fix for potential out-of-bound writes that were possible on `Heap` initialization and `Heap::extend`. See the [security advisory](https://github.com/rust-osdev/linked-list-allocator/security/advisories/GHSA-xg8p-34w2-j49j) for details. The issues were fixed in the following way:

- The initialization functions now panic if the given size is not large enough to store the necessary metadata. Depending on the alignment of the heap bottom pointer, the minimum size is between `2 * size_of::<usize>` and `3 * size_of::<usize>`.
- The `extend` method now panics when trying to extend an unitialized heap.
- Extend calls with a size smaller than `size_of::<usize>() * 2` are now buffered internally and not added to the list directly. The buffered region will be merged with future `extend` calls.
- The `size()` method now returns the _usable_ size of the heap, which might be slightly smaller than the `top() - bottom()` difference because of alignment constraints.

# 0.10.1 – 2022-07-07

- Fixed logic for freeing nodes ([#64])

[#64]: https://github.com/rust-osdev/linked-list-allocator/pull/64

# 0.10.0 – 2022-06-27

- Changed constructor to take `*mut u8` instead of `usize` ([#62])
    - NOTE: Breaking API change
- Reworked internals to pass Miri tests ([#62])

[#62]: https://github.com/phil-opp/linked-list-allocator/pull/62

# 0.9.1 – 2021-10-17

- Add safe constructor and initialization for `Heap` ([#55](https://github.com/phil-opp/linked-list-allocator/pull/55))
- Merge front/back padding after allocate current hole ([#54](https://github.com/phil-opp/linked-list-allocator/pull/54))

# 0.9.0 – 2021-05-01

- Update `spinning_top` dependency to `v0.2.3` ([#50](https://github.com/phil-opp/linked-list-allocator/pull/50))

# 0.8.11 – 2021-01-02

- Add new `use_spin_nightly` feature, which, together with `const_mut_refs`, makes the `empty` method of `LockedHeap` const ([#49](https://github.com/phil-opp/linked-list-allocator/pull/49))

# 0.8.10 – 2020-12-28

- Made hole module public for external uses ([#47](https://github.com/phil-opp/linked-list-allocator/pull/47))

# 0.8.9 – 2020-12-27

- Don't require nightly for `use_spin` feature ([#46](https://github.com/phil-opp/linked-list-allocator/pull/46))

# 0.8.8 – 2020-12-16

- Do not require alloc crate ([#44](https://github.com/phil-opp/linked-list-allocator/pull/44))

# 0.8.7 – 2020-12-10

- _Unstable Breakage:_ fix(alloc_ref): Use new nightly Allocator trait [#42](https://github.com/phil-opp/linked-list-allocator/pull/42)
- Build on stable without features [#43](https://github.com/phil-opp/linked-list-allocator/pull/43)
  - Adds a new `const_mut_refs` crate feature (enabled by default).
  - By disabling this feature, it's possible to build the crate on stable Rust.

# 0.8.6 – 2020-09-24

- Fix build error on latest nightly ([#35](https://github.com/phil-opp/linked-list-allocator/pull/35))

# 0.8.5 – 2020-08-13

- Update AllocRef implementation for latest API changes ([#33](https://github.com/phil-opp/linked-list-allocator/pull/33))

# 0.8.4

- Add function to get used and free heap size ([#32](https://github.com/phil-opp/linked-list-allocator/pull/32))

# 0.8.3

- Prevent writing to heap memory range when size too small ([#31](https://github.com/phil-opp/linked-list-allocator/pull/31))

# 0.8.2

- Update AllocRef implementation for latest API changes ([#30](https://github.com/phil-opp/linked-list-allocator/pull/30))

# 0.8.1

- AllocRef::alloc is now safe and allows zero-sized allocations ([#28](https://github.com/phil-opp/linked-list-allocator/pull/28))
    - This is technically a **breaking change** for the unstable `alloc_ref` feature of this crate because it now requires a newer nightly version of Rust.

# 0.8.0

- **Breaking**: Make AllocRef implementation optional behind new `alloc_ref` feature
    - To enable the `AllocRef` implementation again, enable the `alloc_ref` feature of this crate in your Cargo.toml
- Fix build on nightly 1.43.0 (05-03-2020) ([#25](https://github.com/phil-opp/linked-list-allocator/pull/25))

# 0.7.0

- Use new spinning_top crate instead of `spin` ([#23](https://github.com/phil-opp/linked-list-allocator/pull/23))

# 0.6.6

- The `Alloc` trait was renamed to `AllocRef` ([#20](https://github.com/phil-opp/linked-list-allocator/pull/20))

# 0.6.5

- Align up the Hole initialization address ([#18](https://github.com/phil-opp/linked-list-allocator/pull/18))
- Remove `alloc` feature gate, which is now stable
