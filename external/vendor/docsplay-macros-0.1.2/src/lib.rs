//! Derive macro implementation
#![doc(html_root_url = "https://docs.rs/docsplay/0.1.0")]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(
    rust_2018_idioms,
    unreachable_pub,
    bad_style,
    dead_code,
    improper_ctypes,
    non_shorthand_field_patterns,
    no_mangle_generic_items,
    overflowing_literals,
    path_statements,
    patterns_in_fns_without_body,
    unconditional_recursion,
    unused,
    unused_allocation,
    unused_comparisons,
    unused_parens,
    while_true
)]
#![allow(clippy::try_err)]

#[allow(unused_extern_crates)]
extern crate proc_macro;

mod attr;
mod expand;
mod fmt;

use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput};

/// [Custom `#[derive(...)]` macro](https://doc.rust-lang.org/edition-guide/rust-2018/macros/custom-derive.html)
/// for implementing [`fmt::Display`][core::fmt::Debug] via doc comment attributes.
///
/// ## Generic Type Parameters
///
/// Type parameters to an enum or struct using this macro should *not* need to
/// have an explicit `Display` constraint at the struct or enum definition
/// site. A `Display` implementation for the `derive`d struct or enum is
/// generated assuming each type parameter implements `Display`, but that should
/// be possible without adding the constraint to the struct definition itself:
///
/// ```rust,ignore
/// use docsplay::Display;
///
/// /// oh no, an error: {0}
/// #[derive(Display)]
/// pub struct Error<E>(pub E);
///
/// // No need to require `E: Display`, since `docsplay::Display` adds that implicitly.
/// fn generate_error<E>(e: E) -> Error<E> { Error(e) }
///
/// assert!("oh no, an error: muahaha" == &format!("{}", generate_error("muahaha")));
/// ```
///
/// ## Using [`Debug`][core::fmt::Debug] Implementations with Type Parameters
/// However, if a type parameter must instead be constrained with the
/// [`Debug`][core::fmt::Debug] trait so that some field may be printed with
/// `{:?}`, that constraint must currently still also be specified redundantly
/// at the struct or enum definition site. If a struct or enum field is being
/// formatted with `{:?}` via `docsplay`, and a generic type
/// parameter must implement `Debug` to do that, then that struct or enum
/// definition will need to propagate the `Debug` constraint to every type
/// parameter it's instantiated with:
///
/// ```rust,ignore
/// use core::fmt::Debug;
/// use docsplay::Display;
///
/// /// oh no, an error: {0:?}
/// #[derive(Display)]
/// pub struct Error<E: Debug>(pub E);
///
/// // `E: Debug` now has to propagate to callers.
/// fn generate_error<E: Debug>(e: E) -> Error<E> { Error(e) }
///
/// assert!("oh no, an error: \"cool\"" == &format!("{}", generate_error("cool")));
///
/// // Try this with a struct that doesn't impl `Display` at all, unlike `str`.
/// #[derive(Debug)]
/// pub struct Oh;
/// assert!("oh no, an error: Oh" == &format!("{}", generate_error(Oh)));
/// ```
#[proc_macro_derive(
    Display,
    attributes(ignore_extra_doc_attributes, prefix_enum_doc_attributes, display)
)]
pub fn derive_error(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    expand::derive(&input)
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}
