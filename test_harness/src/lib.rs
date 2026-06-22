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
use proc_macro2::Span;
use quote::quote;
use std::sync::atomic::{AtomicBool, Ordering};
use syn::{
    parse::Parser, parse_macro_input, punctuated::Punctuated, token::Comma, Expr, ExprLit, FnArg,
    ItemFn, Lit, LitStr, Meta,
};

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

#[proc_macro_attribute]
pub fn ignore(_attr: TokenStream, _item: TokenStream) -> TokenStream {
    let expanded = quote! {};
    return TokenStream::from(expanded);
}

fn generate_test_case(attr: TokenStream, item: TokenStream) -> TokenStream {
    let test_config = match parse_test_config(attr) {
        Ok(config) => config,
        Err(e) => return e.to_compile_error().into(),
    };
    let repeat_count = test_config.repeat_count;
    let thread_count = test_config.thread_count;
    let exclusive_buddy = test_config.exclusive_buddy;
    let input = parse_macro_input!(item as ItemFn);
    let test_name = &input.sig.ident;
    let input_block = &input.block;

    let mut passthrough_attrs = Vec::new();
    let mut ignore_reason: Option<LitStr> = None;

    for attr in input.attrs.into_iter() {
        if attr.path().is_ident("ignore") {
            let reason = match &attr.meta {
                Meta::Path(_) => LitStr::new("", Span::call_site()),
                Meta::NameValue(name_value) => match &name_value.value {
                    Expr::Lit(ExprLit {
                        lit: Lit::Str(lit_str),
                        ..
                    }) => lit_str.clone(),
                    _ => LitStr::new("", Span::call_site()),
                },
                _ => LitStr::new("", Span::call_site()),
            };
            ignore_reason = Some(reason);
            continue;
        }

        passthrough_attrs.push(attr);
    }

    let filtered_params = input
        .sig
        .inputs
        .iter()
        .filter(|arg| !matches!(arg, FnArg::Receiver(_)));

    let param_names = filtered_params.clone().filter_map(|arg| match arg {
        FnArg::Typed(pat_type) => Some(&pat_type.pat),
        _ => None,
    });

    let ignore_guard = ignore_reason.map(|reason| {
        quote! {
            {
                let msg: &str = #reason;
                if msg.is_empty() {
                    println!("[  IGNORED ] {}", stringify!(#test_name));
                } else {
                    println!("[  IGNORED ] {} - {}", stringify!(#test_name), msg);
                }
                return;
            }
        }
    });

    let exclusion_guard = if exclusive_buddy {
        quote! {
            let _blueos_buddy_exclusion_guard = blueos::BUDDY_EXCLUSION.write();
        }
    } else {
        quote! {
            let _blueos_buddy_exclusion_guard = blueos::BUDDY_EXCLUSION.read();
        }
    };

    let test_body = if thread_count == 1 && repeat_count == 1 {
        quote! {
            println!("[ RUN      ] {}", stringify!(#test_name));
            #input_block
            println!("[       OK ] {}", stringify!(#test_name));
        }
    } else if thread_count == 1 {
        quote! {
            for __blueos_repeat_idx in 0..#repeat_count {
                println!(
                    "[ RUN      ] {} [{}/{}]",
                    stringify!(#test_name),
                    __blueos_repeat_idx + 1,
                    #repeat_count
                );
                #input_block
                println!(
                    "[       OK ] {} [{}/{}]",
                    stringify!(#test_name),
                    __blueos_repeat_idx + 1,
                    #repeat_count
                );
            }
        }
    } else {
        let barrier_count = thread_count + 1;
        let build_threaded_test_body = || {
            quote! {
                {
                    struct __BlueOSTestDoneGuard {
                        done: blueos::types::Arc<core::sync::atomic::AtomicUsize>,
                    }

                    impl Drop for __BlueOSTestDoneGuard {
                        fn drop(&mut self) {
                            self.done.fetch_add(1, core::sync::atomic::Ordering::Release);
                            blueos::sync::wake(&self.done);
                        }
                    }

                    let __blueos_done =
                        blueos::types::Arc::new(core::sync::atomic::AtomicUsize::new(0));
                    let __blueos_start =
                        blueos::types::Arc::new(blueos::sync::ConstBarrier::<#barrier_count>::new());
                    for __blueos_thread_idx in 0..#thread_count {
                        let __blueos_done = __blueos_done.clone();
                        let __blueos_start = __blueos_start.clone();
                        blueos::thread::spawn(move || {
                            let _ = __blueos_thread_idx;
                            __blueos_start.wait();
                            let _blueos_done_guard =
                                __BlueOSTestDoneGuard { done: __blueos_done };
                            #input_block
                        })
                        .expect("failed to spawn test thread");
                    }
                    __blueos_start.wait();
                    blueos::sync::wait_until(#thread_count, &__blueos_done);
                }
            }
        };

        if repeat_count == 1 {
            let threaded_test_body = build_threaded_test_body();
            quote! {
                println!(
                    "[ RUN      ] {} [threads={}]",
                    stringify!(#test_name),
                    #thread_count
                );
                #threaded_test_body
                println!(
                    "[       OK ] {} [threads={}]",
                    stringify!(#test_name),
                    #thread_count
                );
            }
        } else {
            let threaded_test_body = build_threaded_test_body();
            quote! {
                for __blueos_repeat_idx in 0..#repeat_count {
                    println!(
                        "[ RUN      ] {} [{}/{}, threads={}]",
                        stringify!(#test_name),
                        __blueos_repeat_idx + 1,
                        #repeat_count,
                        #thread_count
                    );
                    #threaded_test_body
                    println!(
                        "[       OK ] {} [{}/{}, threads={}]",
                        stringify!(#test_name),
                        __blueos_repeat_idx + 1,
                        #repeat_count,
                        #thread_count
                    );
                }
            }
        }
    };

    let expanded = quote! {
        #(#passthrough_attrs)*
        #[test_case]
        fn #test_name(#(#filtered_params),*) {
            #[cfg(not(use_defmt))]
            use semihosting::println;
            #[cfg(use_defmt)]
            use defmt::println as println;
            #( let _ = #param_names; )*
            #exclusion_guard
            #ignore_guard
            #test_body
        }
    };
    expanded.into()
}

#[derive(Clone, Copy, Debug)]
struct TestConfig {
    repeat_count: usize,
    thread_count: usize,
    exclusive_buddy: bool,
}

fn parse_test_config(attr: TokenStream) -> Result<TestConfig, syn::Error> {
    if attr.is_empty() {
        return Ok(TestConfig {
            repeat_count: 1,
            thread_count: 1,
            exclusive_buddy: false,
        });
    }

    let parser = Punctuated::<Meta, Comma>::parse_terminated;
    let metas = parser.parse2(attr.into())?;
    let mut config = TestConfig {
        repeat_count: 1,
        thread_count: 1,
        exclusive_buddy: false,
    };
    let mut seen_repeat = false;
    let mut seen_thread = false;
    let mut seen_exclusive = false;

    for meta in metas {
        match meta {
            Meta::NameValue(name_value) if name_value.path.is_ident("repeat") => {
                if seen_repeat {
                    return Err(syn::Error::new_spanned(
                        name_value,
                        "`repeat` can only be specified once",
                    ));
                }
                config.repeat_count = parse_usize_attr(&name_value, "repeat")?;
                seen_repeat = true;
            }
            Meta::NameValue(name_value) if name_value.path.is_ident("thread") => {
                if seen_thread {
                    return Err(syn::Error::new_spanned(
                        name_value,
                        "`thread` can only be specified once",
                    ));
                }
                config.thread_count = parse_usize_attr(&name_value, "thread")?;
                seen_thread = true;
            }
            Meta::NameValue(name_value) if name_value.path.is_ident("exclusive") => {
                if seen_exclusive {
                    return Err(syn::Error::new_spanned(
                        name_value,
                        "`exclusive` can only be specified once",
                    ));
                }
                config.exclusive_buddy = parse_exclusive_attr(&name_value)?;
                seen_exclusive = true;
            }
            other => {
                return Err(syn::Error::new_spanned(
                    other,
                    "unsupported test attribute, expected #[test(repeat = N, thread = M, exclusive = \"buddy\")]",
                ));
            }
        }
    }
    Ok(config)
}

fn parse_usize_attr(name_value: &syn::MetaNameValue, name: &str) -> Result<usize, syn::Error> {
    let Expr::Lit(ExprLit {
        lit: Lit::Int(lit_int),
        ..
    }) = &name_value.value
    else {
        return Err(syn::Error::new_spanned(
            name_value,
            format!("`{name}` expects an integer literal"),
        ));
    };
    let parsed = lit_int.base10_parse::<usize>()?;
    if parsed == 0 {
        return Err(syn::Error::new_spanned(
            lit_int,
            format!("`{name}` must be greater than 0"),
        ));
    }
    Ok(parsed)
}

fn parse_exclusive_attr(name_value: &syn::MetaNameValue) -> Result<bool, syn::Error> {
    let Expr::Lit(ExprLit {
        lit: Lit::Str(lit_str),
        ..
    }) = &name_value.value
    else {
        return Err(syn::Error::new_spanned(
            name_value,
            "`exclusive` expects a string literal",
        ));
    };

    match lit_str.value().as_str() {
        "buddy" => Ok(true),
        _ => Err(syn::Error::new_spanned(
            lit_str,
            "unsupported exclusive test group, expected \"buddy\"",
        )),
    }
}
