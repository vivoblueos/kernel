// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{
    parse::Parser, parse_macro_input, punctuated::Punctuated, token::Comma, Expr, ExprLit,
    ItemStatic, Lit, Meta, StaticMutability,
};

#[proc_macro]
pub fn current_board_mod(_item: TokenStream) -> TokenStream {
    let Ok(board_name) = std::env::var("TARGET_BOARD") else {
        panic!("TARGET_BOARD is not set");
    };

    let mod_ident = syn::Ident::new(&board_name, proc_macro2::Span::call_site());

    quote::quote! {
        pub mod #mod_ident;
        pub use #mod_ident::*;
    }
    .into()
}

/// Defines an interrupt service routine (ISR) and registers it to the specified interrupt number.
///
/// EXAMPLE:
/// ```
/// struct RxIsr;
///
/// #[blueos_macro::interrupt(no = 1)]
/// static RX_ISR: RxIsr = RxIsr;
///
/// impl blueos_hal::isr::IsrDesc for RxIsr {
///    fn service_isr(&self) {
///       // ISR implementation
///   }
/// }
/// ```
#[proc_macro_attribute]
pub fn interrupt(attr: TokenStream, item: TokenStream) -> TokenStream {
    let no = match parse_interrupt_no(attr) {
        Ok(no) => no,
        Err(e) => return e.to_compile_error().into(),
    };

    let item_static = parse_macro_input!(item as ItemStatic);
    if matches!(item_static.mutability, StaticMutability::Mut(_)) {
        return syn::Error::new_spanned(
            &item_static,
            "#[interrupt] only supports immutable `static` items",
        )
        .to_compile_error()
        .into();
    }

    let ident = &item_static.ident;
    let reg_ident = format_ident!("__BLUEOS_INTERRUPT_REG_{}", ident);
    let section = format!(".isr.reg.{no}");

    quote! {
        #item_static

        const _: () = {
            #[repr(C)]
            struct __BlueOsInterruptReg {
                no: usize,
                desc: &'static dyn ::blueos_hal::isr::IsrDesc,
            }

            #[used]
            #[unsafe(link_section = #section)]
            static #reg_ident: blueos_hal::isr::IsrReg = blueos_hal::isr::IsrReg {
                no: #no,
                desc: &#ident as &'static dyn ::blueos_hal::isr::IsrDesc,
            };
        };
    }
    .into()
}

fn parse_interrupt_no(attr: TokenStream) -> Result<usize, syn::Error> {
    let parser = Punctuated::<Meta, Comma>::parse_terminated;
    let metas = parser.parse2(attr.into())?;
    let mut no: Option<usize> = None;

    for meta in metas {
        match meta {
            Meta::NameValue(name_value) if name_value.path.is_ident("no") => {
                if no.is_some() {
                    return Err(syn::Error::new_spanned(
                        name_value,
                        "`no` can only be specified once",
                    ));
                }
                let Expr::Lit(ExprLit {
                    lit: Lit::Int(lit_int),
                    ..
                }) = name_value.value
                else {
                    return Err(syn::Error::new_spanned(
                        name_value,
                        "`no` expects an integer literal, e.g. #[interrupt(no = 1)]",
                    ));
                };
                no = Some(lit_int.base10_parse::<usize>()?);
            }
            other => {
                return Err(syn::Error::new_spanned(
                    other,
                    "unsupported interrupt attribute, expected #[interrupt(no = N)]",
                ));
            }
        }
    }

    no.ok_or_else(|| {
        syn::Error::new(
            proc_macro2::Span::call_site(),
            "missing `no` in #[interrupt]",
        )
    })
}
