<!-- cargo-sync-readme start -->


# Maybe-Async-Cfg Procedure Macro

**Why bother writing similar code twice for blocking and async code?**

[![Build Status](https://github.com/nvksv/maybe-async-cfg/actions/workflows/rust.yml/badge.svg?branch=main)](https://github.com/nvksv/maybe-async-cfg/actions)
[![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE)
[![Latest Version](https://img.shields.io/crates/v/maybe-async-cfg.svg)](https://crates.io/crates/maybe-async-cfg)
[![maybe-async](https://docs.rs/maybe-async-cfg/badge.svg)](https://docs.rs/maybe-async-cfg)

When implementing both sync and async versions of API in a crate, most API of the two version
are almost the same except for some async/await keyword.

`maybe-async-cfg` help unifying async and sync implementation by **procedural macro**.
- Write async code with normal `async`, `await`, and let `maybe_async_cfg` handles those `async`
and `await` when you need a blocking code.
- Add `maybe` attributes and specify feature-based conditions under which sync or async code 
should be generated.
- Use `only_if` (or `remove_if`) to keep code in specified version if necessary.

The `maybe` procedural macro can be applied to the following codes:
- use declaration
- trait declaration
- trait implementation
- function definition
- struct and enum definition
- modules

**RECOMMENDATION**: Enable **resolver ver2** in your crate, which is introduced in Rust 1.51. If
not, two crates in dependency with conflict version (one async and another blocking) can fail
compilation.


## Motivation

The async/await language feature alters the async world of rust. Comparing with the map/and_then
style, now the async code really resembles sync version code.

In many crates, the async and sync version of crates shares the same API, but the minor
difference that all async code must be awaited prevent the unification of async and sync code.
In other words, we are forced to write an async and an sync implementation respectively.


## Macros in Detail

To use `maybe-async-cfg`, we must know which block of codes is only used on sync implementation,
and which on async. These two versions of the implementation should share the same function
signatures except for async/await keywords.

Use `maybe` macro for code that is the same in both async and sync versions except for
async/await keywords. Specify in the macro parameters the conditions (based on features) under
which async and/or sync versions of the code should appear.

- attribute macro **`maybe`**

    Offers a unified way to provide sync and async conversion on demand depending on features,
enabled for your crate, with **async first** policy.

    ```toml
    [dependencies]
    maybe_async_cfg = "0.2"

    [features]
    use_sync = []
    use_async = []
    ```

    In this and all the following examples, we use two features. But you can use any conditions
that are convenient for you, for example, replacing `feature="use_sync"` with
`not(feature="use_async")` everywhere. Feel free, `maybe-async-cfg` does not analyze the
conditions in any way, just substituting them as is.

    Add the `maybe` attribute before all the items that need to be changed in different versions
of the code (sync or async).

    Want to keep async code? Specify the `async` parameter with the condition (based on
features) when your code should be async.

    Wanna convert async code to sync? Specify the `sync` parameter with the condition when the
sync code should be generated.

    ```rust
    #[maybe_async_cfg::maybe(
        idents(Foo),
        sync(feature="use_sync"),
        async(feature="use_async")
    )]
    struct Struct {
        f: Foo,
    }
    ```
    After conversion:
    ```rust
    #[cfg(feature="use_sync")]
    struct StructSync {
        f: FooSync,
    }
    #[cfg(feature="use_async")]
    struct StructAsync {
        f: FooAsync,
    }
    ```

- procedural macro **`content`**

    The `content` macro allows you to specify common parameters for many `maybe` macros. Use the
internal `default` attribute with the required parameters inside the `content` macro.

    ```rust
    maybe_async_cfg::content!{
    #![maybe_async_cfg::default(
        idents(Foo, Bar),
    )]

    #[maybe_async_cfg::maybe(
        sync(feature="use_sync"), 
        async(feature="use_async")
    )]
    struct Struct {
        f: Foo,
    }

    #[maybe_async_cfg::maybe(
        sync(feature="use_sync"), 
        async(feature="use_async")
    )]
    async fn func(b: Bar) {
        todo!()
    }
    } // content!
    ```
    After conversion:
    ```rust
    #[cfg(feature="use_sync")]
    struct StructSync {
        f: FooSync,
    }
    #[cfg(feature="use_async")]
    struct StructAsync {
        f: FooAsync,
    }

    #[cfg(feature="use_sync")]
    fn func_sync(b: BarSync) {
        todo!()
    }
    #[cfg(feature="use_async")]
    async fn func_async(b: BarAsync) {
        todo!()
    }
    ```

## Doctests
    
When writing doctests, you can mark them as applicable only in the corresponding code version. 
To do this, specify `only_if(`_VARIANT_KEY_`)` in the doctest attributes. Then in all other
versions of the code, this doctest will be replaced with an empty string.

```rust
#[maybe_async_cfg::maybe(
    idents(Foo),
    sync(feature="use_sync"),
    async(feature="use_async")
)]
/// This is a structure. 
/// ```rust, only_if(sync)
/// let s = StructSync{ f: FooSync::new() };
/// ```
/// ```rust, only_if(async)
/// let s = StructAsync{ f: FooAsync::new().await };
/// ```
struct Struct {
    f: Foo,
}
```
After conversion:
```rust
#[cfg(feature="use_sync")]
/// This is a structure. 
/// ```rust, only_if(sync)
/// let s = StructSync{ f: FooSync::new() };
/// ```
///
struct StructSync {
f: FooSync,
}
#[cfg(feature="use_async")]
/// This is a structure. 
///
/// ```rust, only_if(async)
/// let s = StructAsync{ f: FooAsync::new().await };
/// ```
struct StructAsync {
    f: FooAsync,
}
```

## Examples

### rust client for services

When implementing rust client for any services, like awz3. The higher level API of async and
sync version is almost the same, such as creating or deleting a bucket, retrieving an object and
etc.

The example `service_client` is a proof of concept that `maybe_async_cfg` can actually free us
from writing almost the same code for sync and async. We can toggle between a sync AWZ3 client
and async one by `is_sync` feature gate when we add `maybe-async-cfg` to dependency.


## Acknowledgements

This crate is a redesigned fork of these wonderful crates:

- [fMeow/maybe-async-rs](https://github.com/fMeow/maybe-async-rs)

- [marioortizmanero/maybe-async-rs](https://github.com/marioortizmanero/maybe-async-rs)

Thanks!


# License
MIT

<!-- cargo-sync-readme end -->
