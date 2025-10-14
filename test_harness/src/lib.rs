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

extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use std::sync::atomic::{AtomicBool, Ordering};
use syn::{parse_macro_input, FnArg, ItemFn};

static ENABLE_TEST_ONLY: AtomicBool = AtomicBool::new(false);
static HAS_ONLY_TEST: AtomicBool = AtomicBool::new(false);

#[proc_macro]
pub fn test_only(_input: TokenStream) -> TokenStream {
    ENABLE_TEST_ONLY.store(true, Ordering::Release);
    let expanded = quote! {};
    TokenStream::from(expanded)
}

#[proc_macro_attribute]
pub fn test(attr: TokenStream, item: TokenStream) -> TokenStream {
    if ENABLE_TEST_ONLY.load(Ordering::Acquire) {
        let expanded = quote! {};
        return TokenStream::from(expanded);
    }

    generate_test_case(attr, item)
}

#[proc_macro_attribute]
pub fn only_test(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !ENABLE_TEST_ONLY.load(Ordering::Acquire) {
        let expanded = quote! {};
        return TokenStream::from(expanded);
    }

    if HAS_ONLY_TEST
        .compare_exchange(false, true, Ordering::SeqCst, Ordering::Relaxed)
        .is_err()
    {
        let expanded = quote! {};
        return TokenStream::from(expanded);
    }

    generate_test_case(attr, item)
}

fn generate_test_case(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let test_name = &input.sig.ident;
    let input_block = &input.block;

    let filtered_params = input
        .sig
        .inputs
        .iter()
        .filter(|arg| !matches!(arg, FnArg::Receiver(_)));

    let param_names = filtered_params.clone().filter_map(|arg| match arg {
        FnArg::Typed(pat_type) => Some(&pat_type.pat),
        _ => None,
    });

    let expanded = quote! {
        #[test_case]
        fn #test_name(#(#filtered_params),*) {
            #[cfg(not(use_defmt))]
            use semihosting::println;
            #[cfg(use_defmt)]
            use defmt::println as println;
            println!("[ RUN      ] {}", stringify!(#test_name));
            #( let _ = #param_names; )*
            #input_block
            println!("[       OK ] {}", stringify!(#test_name));
        }
    };
    expanded.into()
}
