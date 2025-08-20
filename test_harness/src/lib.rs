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
use syn::{parse_macro_input, FnArg, ItemFn};

#[proc_macro_attribute]
pub fn test(_attr: TokenStream, item: TokenStream) -> TokenStream {
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
            use semihosting::println;
            println!("[ RUN      ] {}", stringify!(#test_name));
            #( let _ = #param_names; )*
            #input_block
            println!("[       OK ] {}", stringify!(#test_name));
        }
    };
    expanded.into()
}
