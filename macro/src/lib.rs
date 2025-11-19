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
use quote::quote;
use syn::{Data, Field, Fields};

#[proc_macro]
pub fn current_board_mod(_item: TokenStream) -> TokenStream {
    let Some(board_name) = std::env::var("TARGET_BOARD") else {
        panic!("TARGET_BOARD is not set");
    };

    let mod_ident = syn::Ident::new(&board_name, proc_macro2::Span::call_site());

    quote::quote! {
        pub mod #mod_ident;
        pub use #mod_ident::*;
    }
    .into()
}
