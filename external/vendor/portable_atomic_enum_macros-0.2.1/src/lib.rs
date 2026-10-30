#![forbid(
    rust_2018_idioms,
    future_incompatible,
    elided_lifetimes_in_paths,
    unsafe_code
)]
#![warn(
    missing_debug_implementations,
    missing_docs,
    trivial_casts,
    trivial_numeric_casts,
    unreachable_pub,
    unused_import_braces,
    unused_qualifications
)]

//! An attribute to create an atomic wrapper around a C-style enum.
//!
//! Internally, the generated wrapper uses an `AtomicUsize` to store the value.
//! The atomic operations have the same semantics as the equivalent operations
//! of `AtomicUsize`.
//!
//! # Example
//!
//! ```
//! # use portable_atomic_enum::atomic_enum;
//! # use std::sync::atomic::Ordering;
//! #[atomic_enum]
//! #[derive(PartialEq)]
//! enum CatState {
//!     Dead = 0,
//!     BothDeadAndAlive,
//!     Alive,
//! }
//!
//! let state = AtomicCatState::new(CatState::Dead);
//! state.store(CatState::Alive, Ordering::Relaxed);
//!
//! assert_eq!(state.load(Ordering::Relaxed), CatState::Alive);
//! ```
//!
//! This attribute does not use or generate any unsafe code.
//!
//! The crate can be used in a `#[no_std]` environment.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{parse_macro_input, Attribute, Ident, ItemEnum, Variant, Visibility};

fn enum_definition<'a>(
    attrs: impl IntoIterator<Item = Attribute>,
    vis: &Visibility,
    ident: &Ident,
    variants: impl IntoIterator<Item = &'a Variant>,
) -> TokenStream2 {
    let attrs = attrs.into_iter();
    let variants = variants.into_iter();

    quote! {
        #(#attrs)*
        #vis enum #ident {
            #( #variants ),*
        }
    }
}

fn atomic_enum_definition(vis: &Visibility, ident: &Ident, atomic_ident: &Ident) -> TokenStream2 {
    let atomic_ident_docs = format!(
        "A wrapper around [`{ident}`] which can be safely shared between threads.

This type uses an `AtomicUsize` to store the enum value.",
    );

    quote! {
        #[doc = #atomic_ident_docs]
        #vis struct #atomic_ident(portable_atomic_enum::atomic::AtomicUsize);
    }
}

fn enum_to_usize(ident: &Ident) -> TokenStream2 {
    let to_usize_docs = format!("Converts the [`{ident}`] variant to a `usize`.");
    quote! {
        #[doc = #to_usize_docs]
        const fn to_usize(val: #ident) -> usize {
            val as usize
        }
    }
}

fn enum_from_usize(ident: &Ident, variants: impl IntoIterator<Item = Variant>) -> TokenStream2 {
    let from_usize_docs = format!("Converts the `usize` to a [`{ident}`] variant.");

    let variants = variants
        .into_iter()
        .map(|v| v.ident)
        .map(|id| quote! { v if v == #ident::#id as usize => #ident::#id, });

    quote! {
        #[doc = #from_usize_docs]
        fn from_usize(val: usize) -> #ident {
            match val {
                #(#variants)*
                _ => panic!("Invalid enum discriminant"),
            }
        }
    }
}

fn atomic_enum_new(ident: &Ident, atomic_ident: &Ident) -> TokenStream2 {
    let atomic_ident_docs = format!("Creates a new atomic [`{ident}`].");

    quote! {
        #[doc = #atomic_ident_docs]
        pub const fn new(v: #ident) -> #atomic_ident {
            #atomic_ident(portable_atomic_enum::atomic::AtomicUsize::new(Self::to_usize(v)))
        }
    }
}

fn atomic_enum_into_inner(ident: &Ident) -> TokenStream2 {
    quote! {
        /// Consumes the atomic and returns the contained value.
        ///
        /// This is safe because passing self by value guarantees that no other threads are concurrently accessing the atomic data.
        pub fn into_inner(self) -> #ident {
            Self::from_usize(self.0.into_inner())
        }
    }
}

fn atomic_enum_set(ident: &Ident) -> TokenStream2 {
    quote! {
        /// Sets the value of the atomic without performing an atomic operation.
        ///
        /// This is safe because the mutable reference guarantees that no other threads are concurrently accessing the atomic data.
        pub fn set(&mut self, v: #ident) {
            *self.0.get_mut() = Self::to_usize(v);
        }
    }
}

fn atomic_enum_get(ident: &Ident) -> TokenStream2 {
    quote! {
        /// Gets the value of the atomic without performing an atomic operation.
        ///
        /// This is safe because the mutable reference guarantees that no other threads are concurrently accessing the atomic data.
        pub fn get(&mut self) -> #ident {
            Self::from_usize(*self.0.get_mut())
        }
    }
}

fn atomic_enum_swap_mut(ident: &Ident) -> TokenStream2 {
    quote! {
        /// Stores a value into the atomic, returning the previous value, without performing an atomic operation.
        ///
        /// This is safe because the mutable reference guarantees that no other threads are concurrently accessing the atomic data.
        pub fn swap_mut(&mut self, v: #ident) -> #ident {
            let r = self.get();
            self.set(v);
            r
        }
    }
}

fn atomic_enum_load(ident: &Ident) -> TokenStream2 {
    quote! {
        /// Loads a value from the atomic.
        ///
        /// `load` takes an `Ordering` argument which describes the memory ordering of this operation. Possible values are `SeqCst`, `Acquire` and `Relaxed`.
        ///
        /// # Panics
        ///
        /// Panics if order is `Release` or `AcqRel`.
        pub fn load(&self, order: ::core::sync::atomic::Ordering) -> #ident {
            Self::from_usize(self.0.load(order))
        }
    }
}

fn atomic_enum_store(ident: &Ident) -> TokenStream2 {
    quote! {
        /// Stores a value into the atomic.
        ///
        /// `store` takes an `Ordering` argument which describes the memory ordering of this operation. Possible values are `SeqCst`, `Release` and `Relaxed`.
        ///
        /// # Panics
        ///
        /// Panics if order is `Acquire` or `AcqRel`.
        pub fn store(&self, val: #ident, order: ::core::sync::atomic::Ordering) {
            self.0.store(Self::to_usize(val), order)
        }
    }
}

fn atomic_enum_swap(ident: &Ident) -> TokenStream2 {
    quote! {
        /// Stores a value into the atomic, returning the previous value.
        ///
        /// `swap` takes an `Ordering` argument which describes the memory ordering of this operation.
        /// All ordering modes are possible. Note that using `Acquire` makes the store part of this operation `Relaxed`,
        /// and using `Release` makes the load part `Relaxed`.
        pub fn swap(&self, val: #ident, order: ::core::sync::atomic::Ordering) -> #ident {
            Self::from_usize(self.0.swap(Self::to_usize(val), order))
        }
    }
}

fn atomic_enum_compare_exchange(ident: &Ident) -> TokenStream2 {
    quote! {
        /// Stores a value into the atomic if the current value is the same as the `current` value.
        ///
        /// The return value is a result indicating whether the new value was written and containing the previous value.
        /// On success this value is guaranteed to be equal to `current`.
        ///
        /// `compare_exchange` takes two `Ordering` arguments to describe the memory ordering of this operation. The first
        /// describes the required ordering if the operation succeeds while the second describes the required ordering when
        /// the operation fails. Using `Acquire` as success ordering makes the store part of this operation `Relaxed`, and
        /// using `Release` makes the successful load `Relaxed`. The failure ordering can only be `SeqCst`, `Acquire` or
        /// `Relaxed` and must be equivalent to or weaker than the success ordering.
        pub fn compare_exchange(
            &self,
            current: #ident,
            new: #ident,
            success: ::core::sync::atomic::Ordering,
            failure: ::core::sync::atomic::Ordering
        ) -> ::core::result::Result<#ident, #ident> {
            self.0
                .compare_exchange(
                    Self::to_usize(current),
                    Self::to_usize(new),
                    success,
                    failure
                )
                .map(Self::from_usize)
                .map_err(Self::from_usize)
        }
    }
}

fn atomic_enum_compare_exchange_weak(ident: &Ident) -> TokenStream2 {
    quote! {
        /// Stores a value into the atomic if the current value is the same as the `current` value.
        ///
        /// Unlike `compare_exchange`, this function is allowed to spuriously fail even when the comparison succeeds,
        /// which can result in more efficient code on some platforms. The return value is a result indicating whether
        /// the new value was written and containing the previous value.
        ///
        /// `compare_exchange_weak` takes two `Ordering` arguments to describe the memory ordering of this operation.
        /// The first describes the required ordering if the operation succeeds while the second describes the required
        /// ordering when the operation fails. Using `Acquire` as success ordering makes the store part of this operation
        /// `Relaxed`, and using `Release` makes the successful load `Relaxed`. The failure ordering can only be `SeqCst`,
        /// `Acquire` or `Relaxed` and must be equivalent to or weaker than the success ordering.
        pub fn compare_exchange_weak(
            &self,
            current: #ident,
            new: #ident,
            success: ::core::sync::atomic::Ordering,
            failure: ::core::sync::atomic::Ordering
        ) -> ::core::result::Result<#ident, #ident> {
            self.0
                .compare_exchange_weak(
                    Self::to_usize(current),
                    Self::to_usize(new),
                    success,
                    failure
                )
                .map(Self::from_usize)
                .map_err(Self::from_usize)
        }
    }
}

fn from_impl(ident: &Ident, atomic_ident: &Ident) -> TokenStream2 {
    quote! {
        impl From<#ident> for #atomic_ident {
            fn from(val: #ident) -> #atomic_ident {
                #atomic_ident::new(val)
            }
        }
    }
}

fn debug_impl(atomic_ident: &Ident) -> TokenStream2 {
    quote! {
        impl ::core::fmt::Debug for #atomic_ident {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                ::core::fmt::Debug::fmt(&self.load(::core::sync::atomic::Ordering::SeqCst), f)
            }
        }
    }
}

#[proc_macro_attribute]
/// Creates an atomic wrapper around a C-style enum.
///
/// The generated type is a wrapper around `AtomicUsize` that transparently
/// converts between the stored integer and the enum type. This attribute
/// also automatically derives the `Debug`, `Copy` and `Clone` traits on
/// the enum type.
///
/// The name of the atomic type is the name of the enum type, prefixed with
/// `Atomic`.
///
/// ```
/// # use portable_atomic_enum::atomic_enum;
/// #[atomic_enum]
/// enum State {
///     On,
///     Off,
/// }
///
/// let state = AtomicState::new(State::Off);
/// ```
///
/// The name can be overridden by passing an identifier
/// as an argument to the attribute.
///
/// ```
/// # use portable_atomic_enum::atomic_enum;
/// #[atomic_enum(StateAtomic)]
/// enum State {
///     On,
///     Off,
/// }
///
/// let state = StateAtomic::new(State::Off);
/// ```
pub fn atomic_enum(args: TokenStream, input: TokenStream) -> TokenStream {
    // Parse the input
    let ItemEnum {
        attrs,
        vis,
        ident,
        generics,
        variants,
        ..
    } = parse_macro_input!(input as ItemEnum);

    // We only support C-style enums: No generics, no fields
    if !generics.params.is_empty() {
        return syn::Error::new_spanned(generics, "Expected an enum without generics.")
            .into_compile_error()
            .into();
    }

    for variant in variants.iter() {
        if !matches!(variant.fields, syn::Fields::Unit) {
            return syn::Error::new_spanned(&variant.fields, "Expected a variant without fields.")
                .into_compile_error()
                .into();
        }
    }

    // Define the enum
    let mut output = enum_definition(attrs, &vis, &ident, &variants);

    // Define the atomic wrapper
    let atomic_ident = parse_macro_input!(args as Option<Ident>)
        .unwrap_or_else(|| Ident::new(&format!("Atomic{}", ident), ident.span()));
    output.extend(atomic_enum_definition(&vis, &ident, &atomic_ident));

    // Write the impl block for the atomic wrapper
    let enum_to_usize = enum_to_usize(&ident);
    let enum_from_usize = enum_from_usize(&ident, variants);
    let atomic_enum_new = atomic_enum_new(&ident, &atomic_ident);
    let atomic_enum_into_inner = atomic_enum_into_inner(&ident);
    let atomic_enum_set = atomic_enum_set(&ident);
    let atomic_enum_get = atomic_enum_get(&ident);
    let atomic_enum_swap_mut = atomic_enum_swap_mut(&ident);
    let atomic_enum_load = atomic_enum_load(&ident);
    let atomic_enum_store = atomic_enum_store(&ident);
    let atomic_enum_swap = atomic_enum_swap(&ident);
    let atomic_enum_compare_exchange = atomic_enum_compare_exchange(&ident);
    let atomic_enum_compare_exchange_weak = atomic_enum_compare_exchange_weak(&ident);

    output.extend(quote! {
        impl #atomic_ident {
            #enum_to_usize
            #enum_from_usize
            #atomic_enum_new
            #atomic_enum_into_inner
            #atomic_enum_set
            #atomic_enum_get
            #atomic_enum_swap_mut
            #atomic_enum_load
            #atomic_enum_store
            #atomic_enum_swap
            #atomic_enum_compare_exchange
            #atomic_enum_compare_exchange_weak
        }
    });

    // Implement the from and debug traits
    output.extend(from_impl(&ident, &atomic_ident));
    output.extend(debug_impl(&atomic_ident));

    output.into()
}
