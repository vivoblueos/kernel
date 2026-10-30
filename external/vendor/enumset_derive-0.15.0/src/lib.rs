#![recursion_limit = "256"]

mod const_eval;
mod gen;
mod plan;

extern crate proc_macro;

use proc_macro::TokenStream;
use std::fmt::Display;
use syn::{parse_macro_input, DeriveInput};

/// Helper function for emitting compile errors.
fn error<T>(span: proc_macro2::Span, message: impl Display) -> syn::Result<T> {
    Err(syn::Error::new(span, message))
}

#[proc_macro_derive(EnumSetType, attributes(enumset))]
pub fn derive_enum_set_type(input: TokenStream) -> TokenStream {
    let input: DeriveInput = parse_macro_input!(input);
    derive_enum_set_type_0(input).unwrap_or_else(|e| e.to_compile_error().into())
}
fn derive_enum_set_type_0(input: DeriveInput) -> syn::Result<TokenStream> {
    let plan = plan::plan_for_enum(input)?;
    Ok(gen::generate_code(plan).into())
}
