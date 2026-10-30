# manyhow
## anyhow for proc macros
[![CI Status](https://github.com/ModProg/manyhow/actions/workflows/test.yaml/badge.svg)](https://github.com/ModProg/manyhow/actions/workflows/test.yaml)
[![Crates.io](https://img.shields.io/crates/v/manyhow)](https://crates.io/crates/manyhow)
[![Docs.rs](https://img.shields.io/crates/v/template?color=informational&label=docs.rs)](https://docs.rs/manyhow)
[![Documentation for `main`](https://img.shields.io/badge/docs-main-informational)](https://modprog.github.io/manyhow/manyhow/)

Proc **m**acro **anyhow**, a combination of ideas from
[`anyhow`](https://docs.rs/anyhow) and
[`proc-macro-error`](https://docs.rs/proc-macro-error) to improve proc macro
development, especially focused on the error handling.

## Motivation
Error handling in proc-macros is unideal, as the top level functions of proc
macros can only return `TokenStreams` both in success and failure case. This
means that I often write code like this, moving the actual implementation in
a separate function to be able to use the ergonomic rust error handling with
e.g., `?`.
```rust
use proc_macro2::TokenStream as TokenStream2;
                                                                                           
#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    match actual_implementation(input.into()) {
        Ok(output) => output,
        Err(error) => error.into_compile_error(),
    }
    .into()
}
                                                                                           
fn actual_implementation(input: TokenStream2) -> syn::Result<TokenStream2> {
    // ..
}
```

## Using the `#[manyhow]` macro
To activate the error handling, just add `#[manyhow]` above any
proc macro implementation, reducing the above example to:

```rust
use manyhow::manyhow;
use proc_macro2::TokenStream as TokenStream2;
                                                                                           
#[manyhow]
#[proc_macro]
fn my_macro(input: TokenStream2) -> syn::Result<TokenStream2> {
    // ..
}
```

See [Without macros](#without-macros) to see what this expands to under the
hood.

A proc macro function marked as `#[manyhow]` can take and return any
`TokenStream` and can also return `Result<TokenStream,
E>` where `E` implements `ToTokensError`. As additional parameters a
[dummy](#dummy-mut-tokenstream) and/or [emitter](#emitter-mut-emitter) can
be specified.

The `manyhow` attribute takes one optional flag when used for `proc_macro`
and `proc_macro_attribute`. `#[manyhow(input_as_dummy)]` will take the input
of a function like `proc_macro` to initialize the [dummy `&mut
TokenStream`](#dummy-mut-tokenstream) while `#[manyhow(item_as_dummy)]` on
`proc_macro_attribute` will initialize the dummy with the annotated item.

## Without macros
`manyhow` can be used without proc macros, and they can be disabled by
adding `manyhow` with `default-features=false`.

The usage is more or less the same, though with some added boilerplate from
needing to invoke one of `function`, `attribute` or `derive`
directly.

While the examples use closures, functions can be passed in as well. The
above example would then change to:
```rust
use proc_macro2::TokenStream as TokenStream2;
                                                                                           
#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    manyhow::function(
        input,
        false,
        |input: TokenStream2| -> syn::Result<TokenStream2> {
            // ..
        },
    )
}
```
[`Emitter`](#emitter-mut-emitter) and [dummy
`TokenStream`](#dummy-mut-tokenstream) can also be used. `function` and
`attribute` take an additional boolean parameter controlling whether the
input/item will be used as initial dummy.

## `emitter: &mut Emitter`
`MacroHandler`s (the trait defining what closures/functions can be used
with `manyhow`) can take a mutable reference to an `Emitter`. This
allows to collect errors, but not fail immediately.

`Emitter::into_result` can be used to return if an `Emitter` contains
any values.

```rust
use manyhow::{manyhow, Emitter, ErrorMessage};
use proc_macro2::TokenStream as TokenStream2;
                                                                                           
#[manyhow]
#[proc_macro]
fn my_macro(input: TokenStream2, emitter: &mut Emitter) -> manyhow::Result<TokenStream2> {
    // ..
    emitter.emit(ErrorMessage::call_site("A fun error!"));
    emitter.into_result()?;
    // ..
}
```

## `dummy: &mut TokenStream`
`MacroHandler`s also take a mutable reference to a `TokenStream`, to
enable emitting some dummy code to be used in case the macro errors.

This allows either appending tokens e.g., with `ToTokens::to_tokens` or
directly setting the dummy code e.g., `*dummy = quote!{some tokens}`.
