# linked-list-allocator

[![Crates.io](https://img.shields.io/crates/v/linked-list-allocator)](https://crates.io/crates/linked-list-allocator)
[![Build Status](https://github.com/rust-osdev/linked-list-allocator/workflows/Build/badge.svg)](https://github.com/rust-osdev/linked-list-allocator/actions?query=workflow%3ABuild)
[![docs.rs](https://img.shields.io/badge/docs.rs-documentation-green.svg)](https://docs.rs/linked-list-allocator)

## Usage

Create a static allocator in your root module:

```rust
use linked_list_allocator::LockedHeap;

#[global_allocator]
static ALLOCATOR: LockedHeap = LockedHeap::empty();
```

Before using this allocator, you need to init it:

```rust
pub fn init_heap() {
    let heap_start = …;
    let heap_end = …;
    let heap_size = heap_end - heap_start;
    unsafe {
        ALLOCATOR.lock().init(heap_start, heap_size);
    }
}
```

## Features

- **`use_spin`** (default): Provide a `LockedHeap` type that implements the [`GlobalAlloc`] trait by using a spinlock.
- **`alloc_ref`**: Provide an implementation of the unstable [`AllocRef`] trait; requires nightly Rust.
    - Warning: The `AllocRef` trait is still regularly changed on the Rust side, so expect some regular breakage when using this feature.

[`GlobalAlloc`]: https://doc.rust-lang.org/nightly/core/alloc/trait.GlobalAlloc.html
[`AllocRef`]: https://doc.rust-lang.org/nightly/core/alloc/trait.AllocRef.html

## License
This crate is dual-licensed under MIT or the Apache License (Version 2.0). See LICENSE-APACHE and LICENSE-MIT for details.
