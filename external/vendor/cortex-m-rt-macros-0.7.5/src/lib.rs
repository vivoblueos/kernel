//! Internal implementation details of `cortex-m-rt`.
//!
//! Do not use this crate directly.

extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use std::iter;
use std::{collections::HashSet, fmt::Display};
use syn::{
    parse::{self, Parse},
    parse_macro_input,
    spanned::Spanned,
    AttrStyle, Attribute, FnArg, Ident, Item, ItemFn, ItemStatic, ReturnType, Stmt, Type,
    Visibility,
};

#[proc_macro_attribute]
pub fn entry(args: TokenStream, input: TokenStream) -> TokenStream {
    let mut f = parse_macro_input!(input as ItemFn);

    // check the function signature
    let valid_signature = f.sig.constness.is_none()
        && f.vis == Visibility::Inherited
        && f.sig.abi.is_none()
        && f.sig.inputs.is_empty()
        && f.sig.generics.params.is_empty()
        && f.sig.generics.where_clause.is_none()
        && f.sig.variadic.is_none()
        && match f.sig.output {
            ReturnType::Default => false,
            ReturnType::Type(_, ref ty) => matches!(**ty, Type::Never(_)),
        };

    if !valid_signature {
        return parse::Error::new(
            f.span(),
            "`#[entry]` function must have signature `[unsafe] fn() -> !`",
        )
        .to_compile_error()
        .into();
    }

    if !args.is_empty() {
        return parse::Error::new(Span::call_site(), "This attribute accepts no arguments")
            .to_compile_error()
            .into();
    }

    // XXX should we blacklist other attributes?
    let (statics, stmts) = match extract_static_muts(f.block.stmts) {
        Err(e) => return e.to_compile_error().into(),
        Ok(x) => x,
    };

    f.sig.ident = Ident::new(&format!("__cortex_m_rt_{}", f.sig.ident), Span::call_site());
    f.sig.inputs.extend(statics.iter().map(|statik| {
        let ident = &statik.ident;
        let ty = &statik.ty;
        let attrs = &statik.attrs;

        // Note that we use an explicit `'static` lifetime for the entry point arguments. This makes
        // it more flexible, and is sound here, since the entry will not be called again, ever.
        syn::parse::<FnArg>(
            quote!(#[allow(non_snake_case)] #(#attrs)* #ident: &'static mut #ty).into(),
        )
        .unwrap()
    }));
    f.block.stmts = stmts;

    let tramp_ident = Ident::new(&format!("{}_trampoline", f.sig.ident), Span::call_site());
    let ident = &f.sig.ident;

    let resource_args = statics
        .iter()
        .map(|statik| {
            let (ref cfgs, ref attrs) = extract_cfgs(statik.attrs.clone());
            let ident = &statik.ident;
            let ty = &statik.ty;
            let expr = &statik.expr;
            quote! {
                #(#cfgs)*
                {
                    #(#attrs)*
                    static mut #ident: #ty = #expr;
                    unsafe { &mut #ident }
                }
            }
        })
        .collect::<Vec<_>>();

    if let Err(error) = check_attr_whitelist(&f.attrs, WhiteListCaller::Entry) {
        return error;
    }

    let (ref cfgs, ref attrs) = extract_cfgs(f.attrs.clone());

    quote!(
        #(#cfgs)*
        #(#attrs)*
        #[doc(hidden)]
        #[export_name = "main"]
        pub unsafe extern "C" fn #tramp_ident() {
            #[allow(static_mut_refs)]
            #ident(
                #(#resource_args),*
            )
        }

        #f
    )
    .into()
}

#[derive(Debug, PartialEq)]
enum Exception {
    DefaultHandler,
    HardFault(HardFaultArgs),
    NonMaskableInt,
    Other,
}

impl Display for Exception {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Exception::DefaultHandler => write!(f, "`DefaultHandler`"),
            Exception::HardFault(_) => write!(f, "`HardFault` handler"),
            Exception::NonMaskableInt => write!(f, "`NonMaskableInt` handler"),
            Exception::Other => write!(f, "Other exception handler"),
        }
    }
}

#[derive(Debug, PartialEq)]
struct HardFaultArgs {
    trampoline: bool,
}

impl Default for HardFaultArgs {
    fn default() -> Self {
        Self { trampoline: true }
    }
}

impl Parse for HardFaultArgs {
    fn parse(input: parse::ParseStream) -> syn::Result<Self> {
        let mut items = Vec::new();
        // Read a list of `ident = value,`
        loop {
            if input.is_empty() {
                break;
            }

            let name = input.parse::<Ident>()?;
            input.parse::<syn::Token!(=)>()?;
            let value = input.parse::<syn::Lit>()?;

            items.push((name, value));

            if input.is_empty() {
                break;
            }

            input.parse::<syn::Token!(,)>()?;
        }

        let mut args = Self::default();

        for (name, value) in items {
            match name.to_string().as_str() {
                "trampoline" => match value {
                    syn::Lit::Bool(val) => {
                        args.trampoline = val.value();
                    }
                    _ => {
                        return Err(syn::Error::new_spanned(
                            value,
                            "Not a valid value. `trampoline` takes a boolean literal",
                        ))
                    }
                },
                _ => {
                    return Err(syn::Error::new_spanned(name, "Not a valid argument name"));
                }
            }
        }

        Ok(args)
    }
}

#[proc_macro_attribute]
pub fn exception(args: TokenStream, input: TokenStream) -> TokenStream {
    let mut f = parse_macro_input!(input as ItemFn);

    if let Err(error) = check_attr_whitelist(&f.attrs, WhiteListCaller::Exception) {
        return error;
    }

    let fspan = f.span();
    let ident = f.sig.ident.clone();

    let ident_s = ident.to_string();
    let exn = match &*ident_s {
        "DefaultHandler" => {
            if !args.is_empty() {
                return parse::Error::new(Span::call_site(), "This attribute accepts no arguments")
                    .to_compile_error()
                    .into();
            }
            Exception::DefaultHandler
        }
        "HardFault" => Exception::HardFault(parse_macro_input!(args)),
        "NonMaskableInt" => {
            if !args.is_empty() {
                return parse::Error::new(Span::call_site(), "This attribute accepts no arguments")
                    .to_compile_error()
                    .into();
            }
            Exception::NonMaskableInt
        }
        // NOTE that at this point we don't check if the exception is available on the target (e.g.
        // MemoryManagement is not available on Cortex-M0)
        "MemoryManagement" | "BusFault" | "UsageFault" | "SecureFault" | "SVCall"
        | "DebugMonitor" | "PendSV" | "SysTick" => {
            if !args.is_empty() {
                return parse::Error::new(Span::call_site(), "This attribute accepts no arguments")
                    .to_compile_error()
                    .into();
            }

            Exception::Other
        }
        _ => {
            return parse::Error::new(ident.span(), "This is not a valid exception name")
                .to_compile_error()
                .into();
        }
    };

    if f.sig.unsafety.is_none() {
        match exn {
            Exception::DefaultHandler | Exception::HardFault(_) | Exception::NonMaskableInt => {
                // These are unsafe to define.
                let name = format!("{}", exn);
                return parse::Error::new(ident.span(), format_args!("defining a {} is unsafe and requires an `unsafe fn` (see the cortex-m-rt docs)", name))
                    .to_compile_error()
                    .into();
            }
            Exception::Other => {}
        }
    }

    // Emit a reference to the `Exception` variant corresponding to our exception.
    // This will fail compilation when the target doesn't have that exception.
    let assertion = match exn {
        Exception::Other => {
            quote! {
                const _: () = {
                    let _ = ::cortex_m_rt::Exception::#ident;
                };
            }
        }
        _ => quote!(),
    };

    let handler = match exn {
        Exception::DefaultHandler => {
            let valid_signature = f.sig.constness.is_none()
                && f.vis == Visibility::Inherited
                && f.sig.abi.is_none()
                && f.sig.inputs.len() == 1
                && f.sig.generics.params.is_empty()
                && f.sig.generics.where_clause.is_none()
                && f.sig.variadic.is_none()
                && match f.sig.output {
                    ReturnType::Default => true,
                    ReturnType::Type(_, ref ty) => match **ty {
                        Type::Tuple(ref tuple) => tuple.elems.is_empty(),
                        Type::Never(..) => true,
                        _ => false,
                    },
                };

            if !valid_signature {
                return parse::Error::new(
                    fspan,
                    "`DefaultHandler` must have signature `unsafe fn(i16) [-> !]`",
                )
                .to_compile_error()
                .into();
            }

            f.sig.ident = Ident::new(&format!("__cortex_m_rt_{}", f.sig.ident), Span::call_site());
            let tramp_ident = Ident::new(&format!("{}_trampoline", f.sig.ident), Span::call_site());
            let ident = &f.sig.ident;

            let (ref cfgs, ref attrs) = extract_cfgs(f.attrs.clone());

            quote!(
                #(#cfgs)*
                #(#attrs)*
                #[doc(hidden)]
                #[export_name = #ident_s]
                pub unsafe extern "C" fn #tramp_ident() {
                    extern crate core;

                    const SCB_ICSR: *const u32 = 0xE000_ED04 as *const u32;

                    let irqn = unsafe { (core::ptr::read_volatile(SCB_ICSR) & 0x1FF) as i16 - 16 };

                    #ident(irqn)
                }

                #f
            )
        }
        Exception::HardFault(args) => {
            let valid_signature = f.sig.constness.is_none()
                && f.vis == Visibility::Inherited
                && f.sig.abi.is_none()
                && if args.trampoline {
                    f.sig.inputs.len() == 1
                        && match &f.sig.inputs[0] {
                            FnArg::Typed(arg) => match arg.ty.as_ref() {
                                Type::Reference(r) => {
                                    r.lifetime.is_none() && r.mutability.is_none()
                                }
                                _ => false,
                            },
                            _ => false,
                        }
                } else {
                    f.sig.inputs.is_empty()
                }
                && f.sig.generics.params.is_empty()
                && f.sig.generics.where_clause.is_none()
                && f.sig.variadic.is_none()
                && match f.sig.output {
                    ReturnType::Default => false,
                    ReturnType::Type(_, ref ty) => matches!(**ty, Type::Never(_)),
                };

            if !valid_signature {
                return parse::Error::new(
                    fspan,
                    if args.trampoline {
                        "`HardFault` handler must have signature `unsafe fn(&ExceptionFrame) -> !`"
                    } else {
                        "`HardFault` handler must have signature `unsafe fn() -> !`"
                    },
                )
                .to_compile_error()
                .into();
            }

            f.sig.ident = Ident::new(&format!("__cortex_m_rt_{}", f.sig.ident), Span::call_site());
            let tramp_ident = Ident::new(&format!("{}_trampoline", f.sig.ident), Span::call_site());

            if args.trampoline {
                let ident = &f.sig.ident;

                let (ref cfgs, ref attrs) = extract_cfgs(f.attrs.clone());

                quote!(
                    #(#cfgs)*
                    #(#attrs)*
                    #[doc(hidden)]
                    #[export_name = "_HardFault"]
                    // Only emit link_section when building for embedded targets,
                    // because some hosted platforms (used to check the build)
                    // cannot handle the long link section names.
                    #[cfg_attr(target_os = "none", link_section = ".HardFault.user")]
                    unsafe extern "C" fn #tramp_ident(frame: &::cortex_m_rt::ExceptionFrame) {
                        #ident(frame)
                    }

                    #f

                    // HardFault exceptions are bounced through this trampoline which grabs the stack pointer at
                    // the time of the exception and passes it to the user's HardFault handler in r0.
                    // Depending on the stack mode in EXC_RETURN, fetches stack from either MSP or PSP.
                    core::arch::global_asm!(
                        ".cfi_sections .debug_frame
                        .section .HardFaultTrampoline, \"ax\"
                        .global HardFault
                        .type HardFault,%function
                        .thumb_func
                        .cfi_startproc
                        HardFault:",
                           "mov r0, lr
                            movs r1, #4
                            tst r0, r1
                            bne 0f
                            mrs r0, MSP
                            b _HardFault
                        0:
                            mrs r0, PSP
                            b _HardFault",
                        ".cfi_endproc
                        .size HardFault, . - HardFault",
                    );
                )
            } else {
                quote!(
                    #[doc(hidden)]
                    #[export_name = "_HardFault"]
                    unsafe extern "C" fn #tramp_ident() {
                        // This trampoline has no function except making the compiler diagnostics better.
                    }

                    #[export_name = "HardFault"]
                    // Only emit link_section when building for embedded targets,
                    // because some hosted platforms (used to check the build)
                    // cannot handle the long link section names.
                    #[cfg_attr(target_os = "none", link_section = ".HardFault.user")]
                    #f
                )
            }
        }
        Exception::NonMaskableInt | Exception::Other => {
            let valid_signature = f.sig.constness.is_none()
                && f.vis == Visibility::Inherited
                && f.sig.abi.is_none()
                && f.sig.inputs.is_empty()
                && f.sig.generics.params.is_empty()
                && f.sig.generics.where_clause.is_none()
                && f.sig.variadic.is_none()
                && match f.sig.output {
                    ReturnType::Default => true,
                    ReturnType::Type(_, ref ty) => match **ty {
                        Type::Tuple(ref tuple) => tuple.elems.is_empty(),
                        Type::Never(..) => true,
                        _ => false,
                    },
                };

            if !valid_signature {
                return parse::Error::new(
                    fspan,
                    "`#[exception]` handlers other than `DefaultHandler` and `HardFault` must have \
                     signature `[unsafe] fn() [-> !]`",
                )
                .to_compile_error()
                .into();
            }

            let (statics, stmts) = match extract_static_muts(f.block.stmts) {
                Err(e) => return e.to_compile_error().into(),
                Ok(x) => x,
            };

            f.sig.ident = Ident::new(&format!("__cortex_m_rt_{}", f.sig.ident), Span::call_site());
            f.sig.inputs.extend(statics.iter().map(|statik| {
                let ident = &statik.ident;
                let ty = &statik.ty;
                let attrs = &statik.attrs;
                syn::parse::<FnArg>(
                    quote!(#[allow(non_snake_case)] #(#attrs)* #ident: &mut #ty).into(),
                )
                .unwrap()
            }));
            f.block.stmts = iter::once(
                syn::parse2(quote! {{
                    // check that this exception actually exists
                    ::cortex_m_rt::exception::#ident;
                }})
                .unwrap(),
            )
            .chain(stmts)
            .collect();

            let tramp_ident = Ident::new(&format!("{}_trampoline", f.sig.ident), Span::call_site());
            let ident = &f.sig.ident;

            let resource_args = statics
                .iter()
                .map(|statik| {
                    let (ref cfgs, ref attrs) = extract_cfgs(statik.attrs.clone());
                    let ident = &statik.ident;
                    let ty = &statik.ty;
                    let expr = &statik.expr;
                    quote! {
                        #(#cfgs)*
                        {
                            #(#attrs)*
                            static mut #ident: #ty = #expr;
                            unsafe { &mut #ident }
                        }
                    }
                })
                .collect::<Vec<_>>();

            let (ref cfgs, ref attrs) = extract_cfgs(f.attrs.clone());

            quote!(
                #(#cfgs)*
                #(#attrs)*
                #[doc(hidden)]
                #[export_name = #ident_s]
                pub unsafe extern "C" fn #tramp_ident() {
                    #[allow(static_mut_refs)]
                    #ident(
                        #(#resource_args),*
                    )
                }

                #f
            )
        }
    };

    quote!(
        #assertion
        #handler
    )
    .into()
}

#[proc_macro_attribute]
pub fn interrupt(args: TokenStream, input: TokenStream) -> TokenStream {
    let mut f: ItemFn = syn::parse(input).expect("`#[interrupt]` must be applied to a function");

    if !args.is_empty() {
        return parse::Error::new(Span::call_site(), "This attribute accepts no arguments")
            .to_compile_error()
            .into();
    }

    let fspan = f.span();
    let ident = f.sig.ident.clone();
    let ident_s = ident.to_string();

    // XXX should we blacklist other attributes?

    let valid_signature = f.sig.constness.is_none()
        && f.vis == Visibility::Inherited
        && f.sig.abi.is_none()
        && f.sig.inputs.is_empty()
        && f.sig.generics.params.is_empty()
        && f.sig.generics.where_clause.is_none()
        && f.sig.variadic.is_none()
        && match f.sig.output {
            ReturnType::Default => true,
            ReturnType::Type(_, ref ty) => match **ty {
                Type::Tuple(ref tuple) => tuple.elems.is_empty(),
                Type::Never(..) => true,
                _ => false,
            },
        };

    if !valid_signature {
        return parse::Error::new(
            fspan,
            "`#[interrupt]` handlers must have signature `[unsafe] fn() [-> !]`",
        )
        .to_compile_error()
        .into();
    }

    let (statics, stmts) = match extract_static_muts(f.block.stmts.iter().cloned()) {
        Err(e) => return e.to_compile_error().into(),
        Ok(x) => x,
    };

    f.sig.ident = Ident::new(&format!("__cortex_m_rt_{}", f.sig.ident), Span::call_site());
    f.sig.inputs.extend(statics.iter().map(|statik| {
        let ident = &statik.ident;
        let ty = &statik.ty;
        let attrs = &statik.attrs;
        syn::parse::<FnArg>(quote!(#[allow(non_snake_case)] #(#attrs)* #ident: &mut #ty).into())
            .unwrap()
    }));
    f.block.stmts = iter::once(
        syn::parse2(quote! {{
            // Check that this interrupt actually exists
            interrupt::#ident;
        }})
        .unwrap(),
    )
    .chain(stmts)
    .collect();

    let tramp_ident = Ident::new(&format!("{}_trampoline", f.sig.ident), Span::call_site());
    let ident = &f.sig.ident;

    let resource_args = statics
        .iter()
        .map(|statik| {
            let (ref cfgs, ref attrs) = extract_cfgs(statik.attrs.clone());
            let ident = &statik.ident;
            let ty = &statik.ty;
            let expr = &statik.expr;
            quote! {
                #(#cfgs)*
                {
                    #(#attrs)*
                    static mut #ident: #ty = #expr;
                    unsafe { &mut #ident }
                }
            }
        })
        .collect::<Vec<_>>();

    if let Err(error) = check_attr_whitelist(&f.attrs, WhiteListCaller::Interrupt) {
        return error;
    }

    let (ref cfgs, ref attrs) = extract_cfgs(f.attrs.clone());

    quote!(
        #(#cfgs)*
        #(#attrs)*
        #[doc(hidden)]
        #[export_name = #ident_s]
        pub unsafe extern "C" fn #tramp_ident() {
            #[allow(static_mut_refs)]
            #ident(
                #(#resource_args),*
            )
        }

        #f
    )
    .into()
}

#[proc_macro_attribute]
pub fn pre_init(args: TokenStream, input: TokenStream) -> TokenStream {
    let f = parse_macro_input!(input as ItemFn);

    // check the function signature
    let valid_signature = f.sig.constness.is_none()
        && f.vis == Visibility::Inherited
        && f.sig.unsafety.is_some()
        && f.sig.abi.is_none()
        && f.sig.inputs.is_empty()
        && f.sig.generics.params.is_empty()
        && f.sig.generics.where_clause.is_none()
        && f.sig.variadic.is_none()
        && match f.sig.output {
            ReturnType::Default => true,
            ReturnType::Type(_, ref ty) => match **ty {
                Type::Tuple(ref tuple) => tuple.elems.is_empty(),
                _ => false,
            },
        };

    if !valid_signature {
        return parse::Error::new(
            f.span(),
            "`#[pre_init]` function must have signature `unsafe fn()`",
        )
        .to_compile_error()
        .into();
    }

    if !args.is_empty() {
        return parse::Error::new(Span::call_site(), "This attribute accepts no arguments")
            .to_compile_error()
            .into();
    }

    if let Err(error) = check_attr_whitelist(&f.attrs, WhiteListCaller::PreInit) {
        return error;
    }

    // XXX should we blacklist other attributes?
    let attrs = f.attrs;
    let ident = f.sig.ident;
    let block = f.block;

    quote!(
        #[export_name = "__pre_init"]
        #[allow(missing_docs)]  // we make a private fn public, which can trigger this lint
        #(#attrs)*
        pub unsafe fn #ident() #block
    )
    .into()
}

/// Extracts `static mut` vars from the beginning of the given statements
fn extract_static_muts(
    stmts: impl IntoIterator<Item = Stmt>,
) -> Result<(Vec<ItemStatic>, Vec<Stmt>), parse::Error> {
    let mut istmts = stmts.into_iter();

    let mut seen = HashSet::new();
    let mut statics = vec![];
    let mut stmts = vec![];
    for stmt in istmts.by_ref() {
        match stmt {
            Stmt::Item(Item::Static(var)) => match var.mutability {
                syn::StaticMutability::Mut(_) => {
                    if seen.contains(&var.ident) {
                        return Err(parse::Error::new(
                            var.ident.span(),
                            format!("the name `{}` is defined multiple times", var.ident),
                        ));
                    }

                    seen.insert(var.ident.clone());
                    statics.push(var);
                }
                _ => stmts.push(Stmt::Item(Item::Static(var))),
            },
            _ => {
                stmts.push(stmt);
                break;
            }
        }
    }

    stmts.extend(istmts);

    Ok((statics, stmts))
}

fn extract_cfgs(attrs: Vec<Attribute>) -> (Vec<Attribute>, Vec<Attribute>) {
    let mut cfgs = vec![];
    let mut not_cfgs = vec![];

    for attr in attrs {
        if eq(&attr, "cfg") {
            cfgs.push(attr);
        } else {
            not_cfgs.push(attr);
        }
    }

    (cfgs, not_cfgs)
}

enum WhiteListCaller {
    Entry,
    Exception,
    Interrupt,
    PreInit,
}

fn check_attr_whitelist(attrs: &[Attribute], caller: WhiteListCaller) -> Result<(), TokenStream> {
    let whitelist = &[
        "doc",
        "link_section",
        "cfg",
        "allow",
        "warn",
        "deny",
        "forbid",
        "cold",
        "naked",
        "expect",
    ];

    'o: for attr in attrs {
        for val in whitelist {
            if eq(attr, val) {
                continue 'o;
            }
        }

        let err_str = match caller {
            WhiteListCaller::Entry => "this attribute is not allowed on a cortex-m-rt entry point",
            WhiteListCaller::Exception => {
                "this attribute is not allowed on an exception handler controlled by cortex-m-rt"
            }
            WhiteListCaller::Interrupt => {
                "this attribute is not allowed on an interrupt handler controlled by cortex-m-rt"
            }
            WhiteListCaller::PreInit => {
                "this attribute is not allowed on a pre-init controlled by cortex-m-rt"
            }
        };

        return Err(parse::Error::new(attr.span(), err_str)
            .to_compile_error()
            .into());
    }

    Ok(())
}

/// Returns `true` if `attr.path` matches `name`
fn eq(attr: &Attribute, name: &str) -> bool {
    attr.style == AttrStyle::Outer && attr.path().is_ident(name)
}
