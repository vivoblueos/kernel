[![cargo version](https://img.shields.io/crates/v/portable_atomic_enum.svg)](https://crates.io/crates/portable_atomic_enum) 
[![docs.rs version](https://img.shields.io/docsrs/portable_atomic_enum)](https://docs.rs/atomic_enum/latest/portable_atomic_enum/)
# portable_atomic_enum

This crate is a fork of [atomic_enum](https://github.com/brain0/atomic_enum) and optionally uses
`portable-atomic` to support more targets.

An attribute to create an atomic wrapper around a C-style enum.

Internally, the generated wrapper uses an `AtomicUsize` to store the value.
The atomic operations have the same semantics as the equivalent operations
of `AtomicUsize`.

# Example
```rust
# use atomic_enum::atomic_enum;
# use std::sync::atomic::Ordering;
#[atomic_enum]
#[derive(Clone, Copy, Debug, PartialEq)]
enum CatState {
    Dead = 0,
    BothDeadAndAlive,
    Alive,
}

let state = AtomicCatState::new(CatState::Dead);
state.store(CatState::Alive, Ordering::Relaxed);
assert_eq!(state.load(Ordering::Relaxed), CatState::Alive);
```

This attribute does not use or generate any unsafe code.

The crate can be used in a `#[no_std]` environment.

## Cargo features

- `portable-atomic`: polyfill atomic types using `portable-atomic`
