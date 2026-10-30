//! This module handles generating the actual code to allow an enum type to be used as a bitset.

use crate::plan::{EnumSetInfo, InternalRepr, SerdeRepr};
use proc_macro2::{Literal, Span, TokenStream as SynTokenStream};
use quote::*;
use syn::{Lit, LitInt};

struct Paths {
    enumset: SynTokenStream,
    typed_enumset: SynTokenStream,
    core: SynTokenStream,
    internal: SynTokenStream,
    serde: SynTokenStream,
}
impl Paths {
    fn from(info: &EnumSetInfo) -> Paths {
        let name = &info.name;
        let enumset = match &info.crate_name {
            Some(crate_name) => quote!(::#crate_name),
            None => {
                #[cfg(feature = "proc-macro-crate")]
                {
                    use proc_macro_crate::FoundCrate;

                    let crate_name = proc_macro_crate::crate_name("enumset");
                    match crate_name {
                        Ok(FoundCrate::Name(name)) => {
                            let ident =
                                proc_macro2::Ident::new(&name, proc_macro2::Span::call_site());
                            quote!(::#ident)
                        }
                        _ => quote!(::enumset),
                    }
                }

                #[cfg(not(feature = "proc-macro-crate"))]
                {
                    quote!(::enumset)
                }
            }
        };
        let typed_enumset = quote!(#enumset::EnumSet<#name>);
        let core = quote!(#enumset::__internal::core_export);
        let internal = quote!(#enumset::__internal);
        let serde = quote!(#enumset::__internal::serde);
        Paths { enumset, typed_enumset, core, internal, serde }
    }
}

/// Generates the actual `EnumSetType` impl.
pub fn generate_code(info: EnumSetInfo) -> SynTokenStream {
    let paths = Paths::from(&info);
    let name = &info.name;
    let enumset = &paths.enumset;
    let typed_enumset = &paths.typed_enumset;
    let core = &paths.core;
    let internal = &paths.internal;
    let serde = &paths.serde;
    let is_uninhabited = info.variants.is_empty();

    let repr = match info.internal_repr() {
        InternalRepr::U8 => quote! { u8 },
        InternalRepr::U16 => quote! { u16 },
        InternalRepr::U32 => quote! { u32 },
        InternalRepr::U64 => quote! { u64 },
        InternalRepr::U128 => quote! { u128 },
        InternalRepr::Array(size) => quote! { #internal::ArrayRepr<{ #size }> },
    };
    let variant_map = info.variant_map();
    let all_variants = match info.internal_repr() {
        InternalRepr::U8 | InternalRepr::U16 | InternalRepr::U32 | InternalRepr::U64 => {
            let lit = Literal::u64_unsuffixed(variant_map[0]);
            quote! { #lit }
        }
        InternalRepr::U128 => {
            let lit = Literal::u128_unsuffixed(
                variant_map[0] as u128 | variant_map.get(1).map_or(0, |x| (*x as u128) << 64),
            );
            quote! { #lit }
        }
        InternalRepr::Array(size) => {
            let mut new = Vec::new();
            for i in 0..size {
                new.push(Literal::u64_unsuffixed(*variant_map.get(i).unwrap_or(&0)));
            }
            quote! { #internal::ArrayRepr::<{ #size }>([#(#new,)*]) }
        }
    };

    //
    // Implements operator overloading on the enum type.
    //
    let impl_ops = if info.no_ops {
        quote! {}
    } else {
        quote! {
            #[automatically_derived]
            impl<O: Into<#typed_enumset>> #core::ops::Sub<O> for #name {
                type Output = #typed_enumset;
                fn sub(self, other: O) -> Self::Output {
                    #enumset::EnumSet::only(self) - other.into()
                }
            }
            #[automatically_derived]
            impl<O: Into<#typed_enumset>> #core::ops::BitAnd<O> for #name {
                type Output = #typed_enumset;
                fn bitand(self, other: O) -> Self::Output {
                    #enumset::EnumSet::only(self) & other.into()
                }
            }
            #[automatically_derived]
            impl<O: Into<#typed_enumset>> #core::ops::BitOr<O> for #name {
                type Output = #typed_enumset;
                fn bitor(self, other: O) -> Self::Output {
                    #enumset::EnumSet::only(self) | other.into()
                }
            }
            #[automatically_derived]
            impl<O: Into<#typed_enumset>> #core::ops::BitXor<O> for #name {
                type Output = #typed_enumset;
                fn bitxor(self, other: O) -> Self::Output {
                    #enumset::EnumSet::only(self) ^ other.into()
                }
            }
            #[automatically_derived]
            impl #core::ops::Not for #name {
                type Output = #typed_enumset;
                fn not(self) -> Self::Output {
                    !#enumset::EnumSet::only(self)
                }
            }
            #[automatically_derived]
            impl #core::cmp::PartialEq<#typed_enumset> for #name {
                fn eq(&self, other: &#typed_enumset) -> bool {
                    #enumset::EnumSet::only(*self) == *other
                }
            }
        }
    };

    //
    // Implements serde support.
    //
    let serde_repr = info.serde_repr();
    let impl_serde_ops = match serde_repr {
        SerdeRepr::U8 | SerdeRepr::U16 | SerdeRepr::U32 | SerdeRepr::U64 | SerdeRepr::U128 => {
            let (serialize_repr, from_fn, to_fn) = match serde_repr {
                SerdeRepr::U8 => (quote! { u8 }, quote! { from_u8 }, quote! { to_u8 }),
                SerdeRepr::U16 => (quote! { u16 }, quote! { from_u16 }, quote! { to_u16 }),
                SerdeRepr::U32 => (quote! { u32 }, quote! { from_u32 }, quote! { to_u32 }),
                SerdeRepr::U64 => (quote! { u64 }, quote! { from_u64 }, quote! { to_u64 }),
                SerdeRepr::U128 => (quote! { u128 }, quote! { from_u128 }, quote! { to_u128 }),
                _ => unreachable!(),
            };
            let check_unknown = if info.serialize_deny_unknown {
                quote! {
                    let all_variants_cast =
                        <#repr as #enumset::__internal::EnumSetTypeRepr>::#to_fn(&#all_variants);
                    if value & !all_variants_cast != 0 {
                        use #serde::de::Error;
                        return #core::prelude::v1::Err(
                            D::Error::custom("enumset contains unknown bits")
                        )
                    }
                }
            } else {
                quote! {}
            };
            quote! {
                fn serialize<S: #serde::Serializer>(
                    set: #enumset::EnumSet<#name>, ser: S,
                ) -> #core::result::Result<S::Ok, S::Error> {
                    let value = <#repr as #enumset::__internal::EnumSetTypeRepr>::#to_fn(
                        &#internal::set::get(set),
                    );
                    #serde::Serialize::serialize(&value, ser)
                }
                fn deserialize<'de, D: #serde::Deserializer<'de>>(
                    de: D,
                ) -> #core::result::Result<#enumset::EnumSet<#name>, D::Error> {
                    let value = <#serialize_repr as #serde::Deserialize>::deserialize(de)?;
                    #check_unknown
                    let value = <#repr as #enumset::__internal::EnumSetTypeRepr>::#from_fn(value);
                    #core::prelude::v1::Ok(#internal::set::new(value & #all_variants))
                }
            }
        }
        SerdeRepr::List => {
            let expecting_str = format!("a list of {name}");
            quote! {
                fn serialize<S: #serde::Serializer>(
                    set: #enumset::EnumSet<#name>, ser: S,
                ) -> #core::result::Result<S::Ok, S::Error> {
                    use #serde::ser::SerializeSeq;
                    let mut seq = ser.serialize_seq(#core::prelude::v1::Some(set.len()))?;
                    for bit in set {
                        seq.serialize_element(&bit)?;
                    }
                    seq.end()
                }
                fn deserialize<'de, D: #serde::Deserializer<'de>>(
                    de: D,
                ) -> #core::result::Result<#enumset::EnumSet<#name>, D::Error> {
                    struct Visitor;
                    impl <'de> #serde::de::Visitor<'de> for Visitor {
                        type Value = #enumset::EnumSet<#name>;
                        fn expecting(
                            &self, formatter: &mut #core::fmt::Formatter,
                        ) -> #core::fmt::Result {
                            write!(formatter, #expecting_str)
                        }
                        fn visit_seq<A>(
                            mut self, mut seq: A,
                        ) -> #core::result::Result<Self::Value, A::Error> where
                            A: #serde::de::SeqAccess<'de>
                        {
                            let mut accum = #enumset::EnumSet::<#name>::new();
                            while let #core::prelude::v1::Some(val) = seq.next_element::<#name>()? {
                                accum |= val;
                            }
                            #core::prelude::v1::Ok(accum)
                        }
                    }
                    de.deserialize_seq(Visitor)
                }
            }
        }
        SerdeRepr::Map => {
            let expecting_str = format!("a map from {name} to bool");
            quote! {
                fn serialize<S: #serde::Serializer>(
                    set: #enumset::EnumSet<#name>, ser: S,
                ) -> #core::result::Result<S::Ok, S::Error> {
                    use #serde::ser::SerializeMap;
                    let mut map = ser.serialize_map(#core::prelude::v1::Some(set.len()))?;
                    for bit in set {
                        map.serialize_entry(&bit, &true)?;
                    }
                    map.end()
                }
                fn deserialize<'de, D: #serde::Deserializer<'de>>(
                    de: D,
                ) -> #core::result::Result<#enumset::EnumSet<#name>, D::Error> {
                    struct Visitor;
                    impl <'de> #serde::de::Visitor<'de> for Visitor {
                        type Value = #enumset::EnumSet<#name>;
                        fn expecting(
                            &self, formatter: &mut #core::fmt::Formatter,
                        ) -> #core::fmt::Result {
                            write!(formatter, #expecting_str)
                        }
                        fn visit_map<A>(
                            mut self, mut map: A,
                        ) -> #core::result::Result<Self::Value, A::Error> where
                            A: #serde::de::MapAccess<'de>
                        {
                            let mut accum = #enumset::EnumSet::<#name>::new();
                            while let #core::prelude::v1::Some((val, is_present)) =
                                map.next_entry::<#name, bool>()?
                            {
                                if is_present {
                                    accum |= val;
                                }
                            }
                            #core::prelude::v1::Ok(accum)
                        }
                    }
                    de.deserialize_map(Visitor)
                }
            }
        }
        SerdeRepr::Array => {
            let preferred_size = quote! {
                <<#name as #internal::EnumSetTypePrivate>::Repr as #internal::EnumSetTypeRepr>
                    ::PREFERRED_ARRAY_LEN
            };
            let (check_extra, convert_array) = if info.serialize_deny_unknown {
                (
                    quote! {
                        if _val != 0 {
                        use #serde::de::Error;
                            return #core::prelude::v1::Err(
                                A::Error::custom("enumset contains unknown bits")
                            )
                        }
                    },
                    quote! {
                        use #serde::de::Error;
                        match #enumset::EnumSet::<#name>::try_from_array(accum) {
                            Some(x) => #core::prelude::v1::Ok(x),
                            None => #core::prelude::v1::Err(
                                A::Error::custom("enumset contains unknown bits")
                            ),
                        }
                    },
                )
            } else {
                (quote! {}, quote! {
                    #core::prelude::v1::Ok(#enumset::EnumSet::<#name>::from_array(accum))
                })
            };
            quote! {
                fn serialize<S: #serde::Serializer>(
                    set: #enumset::EnumSet<#name>, ser: S,
                ) -> #core::result::Result<S::Ok, S::Error> {
                    // read the enum as an array
                    let array = set.as_array::<{ #preferred_size }>();

                    // find the last non-zero value in the array
                    let mut end = array.len();
                    for i in (0..array.len()).rev() {
                        if array[i] != 0 {
                            break;
                        }
                        end = i + 1;
                    }

                    // serialize the array
                    #serde::Serialize::serialize(&array[..end], ser)
                }
                fn deserialize<'de, D: #serde::Deserializer<'de>>(
                    de: D,
                ) -> #core::result::Result<#enumset::EnumSet<#name>, D::Error> {
                    struct Visitor;
                    impl <'de> #serde::de::Visitor<'de> for Visitor {
                        type Value = #enumset::EnumSet<#name>;
                        fn expecting(
                            &self, formatter: &mut #core::fmt::Formatter,
                        ) -> #core::fmt::Result {
                            write!(formatter, "a list of u64")
                        }
                        fn visit_seq<A>(
                            mut self, mut seq: A,
                        ) -> #core::result::Result<Self::Value, A::Error> where
                            A: #serde::de::SeqAccess<'de>
                        {
                            let mut accum = [0; #preferred_size];

                            let mut i = 0;
                            while let #core::prelude::v1::Some(val) = seq.next_element::<u64>()? {
                                accum[i] = val;
                                i += 1;

                                if i == accum.len() {
                                    break;
                                }
                            }
                            while let #core::prelude::v1::Some(_val) = seq.next_element::<u64>()? {
                                #check_extra
                            }

                            #convert_array
                        }
                    }
                    de.deserialize_seq(Visitor)
                }
            }
        }
    };

    //
    // Implement the core conversion function that maps enum variants to bits.
    //
    let impl_internal_conversions = create_enum_conversions(&info, &paths);

    //
    // Generate the code for `Eq` and other similar basic traits.
    //
    let impl_basic_traits = if info.no_super_impls {
        quote! {}
    } else {
        let eq_impl = if is_uninhabited {
            quote!(#core::unreachable!(concat!(stringify!(#name), " is uninhabited.")))
        } else {
            quote!((*self as u32) == (*other as u32))
        };

        quote! {
            #[automatically_derived]
            impl #core::cmp::PartialEq for #name {
                fn eq(&self, other: &Self) -> bool {
                    #eq_impl
                }
            }
            #[automatically_derived]
            impl #core::cmp::Eq for #name { }
            #[automatically_derived]
            #[allow(clippy::expl_impl_clone_on_copy)]
            impl #core::clone::Clone for #name {
                fn clone(&self) -> Self {
                    *self
                }
            }
            #[automatically_derived]
            impl #core::marker::Copy for #name { }
        }
    };

    //
    // Generate the code for the explicit repr trait.
    //
    let impl_with_repr = if info.has_explicit_integer_repr() {
        quote! {
            #[automatically_derived]
            unsafe impl #enumset::EnumSetTypeWithRepr for #name {
                type Repr = #repr;
            }
        }
    } else {
        quote! {}
    };

    //
    // Generate the code for compile-time operations.
    //
    let impl_const_opers = create_enum_const_opers(&info, &paths, &repr);

    //
    // Generate the actual enumset trait.
    //
    let mut generated_warnings = SynTokenStream::new();
    for (span, warning) in &info.warnings {
        generated_warnings.extend(quote_spanned! {
            *span => {
                #[deprecated(note = #warning)]
                #[allow(non_upper_case_globals)]
                const _w: () = ();
                let _ = _w;
            }
        });
    }

    let bit_width = info.bit_width();
    let variant_count = info.variants.len() as u32;
    let enum_repr = info.enum_repr();
    let enum_discrim: Vec<_> = info.variants.iter().map(|x| x.discriminant).collect();
    let enum_names: Vec<_> = info.variants.iter().map(|x| &x.name).collect();
    quote! {
        const _: () = {
            // Double check fundamental assumptions baked into a lot of the code here.
            #core::assert!(#core::mem::size_of::<#name>() <= #core::mem::size_of::<#enum_repr>());
            #(#core::assert!(#enum_discrim == (#name::#enum_names as i64));)*

            #[automatically_derived]
            unsafe impl #internal::EnumSetTypePrivate for #name {
                type Repr = #repr;
                const ALL_BITS: Self::Repr = #all_variants;
                const BIT_WIDTH: u32 = #bit_width;
                const VARIANT_COUNT: u32 = #variant_count;

                #impl_internal_conversions

                #internal::__if_serde! {
                    #impl_serde_ops
                }
            }

            #[automatically_derived]
            unsafe impl #enumset::EnumSetType for #name { }

            #impl_ops
            #impl_with_repr
            #impl_basic_traits
            #impl_const_opers

            fn __enumset_derive__generated_warnings() {
                #generated_warnings
            }
        };
    }
}

fn create_enum_conversions(info: &EnumSetInfo, paths: &Paths) -> SynTokenStream {
    let name = &info.name;
    let core = &paths.core;
    let enum_repr = info.enum_repr();

    let hint_is_transmute = quote! {
        #[cfg(target_endian = "little")]
        let r = *(&r as *const #enum_repr as *const #name);

        #[cfg(target_endian = "big")]
        let r = {
            let offset =
                #core::mem::size_of::<#enum_repr>() - #core::mem::size_of::<#name>();
            let r = r << ((offset as #enum_repr) * 8);
            *(&r as *const #enum_repr as *const u8 as *const #name)
        };
    };

    if info.variants.is_empty() {
        // Uninhabited types have no values.
        quote! {
            fn enum_into_u32(self) -> u32 {
                #core::panic!(concat!(stringify!(#name), " is uninhabited."))
            }
            unsafe fn enum_from_u32(val: u32) -> Self {
                #core::panic!(concat!(stringify!(#name), " is uninhabited."))
            }
        }
    } else if info.variants.len() == 1 {
        // Single-variant enums are generally ZSTs in #[repr(Rust)], and can use simpler code.
        let variant = &info.variants[0].name;
        quote! {
            fn enum_into_u32(self) -> u32 {
                self as u32
            }
            unsafe fn enum_from_u32(val: u32) -> Self {
                #name::#variant
            }
        }
    } else if info.uses_lsb_encoding() || info.uses_msb_encoding().is_some() {
        // Prepares output for MSB mode.
        let process_output = if let Some(msb_repr) = info.uses_msb_encoding() {
            quote! {
                let r = (#msb_repr as #enum_repr) - 1 - r;
            }
        } else {
            quote!()
        };

        let (names, values) = if info.bit_width() >= 1000 {
            // This worsens codegen quality, but avoids creating big tables for no good reason.
            let variant_bits: Vec<_> = info.variants.iter().map(|x| x.variant_bit).collect();
            let variant_names: Vec<_> = info
                .variants
                .iter()
                .map(|x| {
                    let variant_name = &x.name;
                    quote! { #name::#variant_name }
                })
                .collect();
            (variant_names, variant_bits)
        } else {
            // Build a table of branches.
            let mut names = Vec::new();
            for i in 0..info.bit_width() {
                // We create invalid transmutes for invalid branches that will never happen.
                // While not very safe, this encourages the compiler to generate a transmute.
                names.push(quote! {{
                    let r = #i as #enum_repr;
                    #process_output
                    #hint_is_transmute
                    r
                }});
            }

            // Fill variants into the table.
            for variant in &info.variants {
                let variant_name = &variant.name;
                names[variant.variant_bit as usize] = quote! { #name::#variant_name };
            }

            let values: Vec<u32> = (0..(names.len() as u32)).collect();

            (names, values)
        };

        quote! {
            #[inline]
            fn enum_into_u32(self) -> u32 {
                let r = self as #enum_repr;
                #process_output
                r as u32
            }
            unsafe fn enum_from_u32(val: u32) -> Self {
                // We put these in const fields so the branches they guard aren't generated even
                // on -O0
                match val {
                    // Every valid variant value has an explicit branch. If they get optimized out,
                    // great. Otherwise, oh well, at least it's safe.
                    #(#values => #names,)*
                    // Default case.
                    _ => #core::hint::unreachable_unchecked(),
                }
            }
        }
    } else if info.uses_mask_encoding() {
        let discriminants: Vec<_> = info
            .variants
            .iter()
            .map(|x| Lit::Int(LitInt::new(x.discriminant.to_string().as_str(), Span::call_site())))
            .collect();
        let variant_names: Vec<_> = info.variants.iter().map(|x| x.name.clone()).collect();
        quote! {
            fn enum_into_u32(self) -> u32 {
                (self as #enum_repr).trailing_zeros()
            }
            unsafe fn enum_from_u32(val: u32) -> Self {
                let val: #enum_repr = 1 << (val as #enum_repr);
                match val {
                    // Every valid variant value has an explicit branch. If they get optimized out,
                    // great. Otherwise, oh well, at least it's safe.
                    #(#discriminants => #name::#variant_names,)*
                    // Default case, hints to the compiler that this is a transmute.
                    r => {
                        let r = r as #enum_repr;
                        #hint_is_transmute
                        r
                    },
                }
            }
        }
    } else if info.uses_compact_encoding() {
        let variant_bits: Vec<_> = info.variants.iter().map(|x| x.variant_bit).collect();
        let variant_names: Vec<_> = info.variants.iter().map(|x| x.name.clone()).collect();
        quote! {
            fn enum_into_u32(self) -> u32 {
                match self {
                    #(#name::#variant_names => #variant_bits,)*
                }
            }
            unsafe fn enum_from_u32(val: u32) -> Self {
                match val {
                    #(#variant_bits => #name::#variant_names,)*
                    _ => #core::hint::unreachable_unchecked(),
                }
            }
        }
    } else {
        unreachable!("Unknown encoding?");
    }
}

fn create_enum_const_opers(
    info: &EnumSetInfo,
    paths: &Paths,
    repr: &SynTokenStream,
) -> SynTokenStream {
    let name = &info.name;
    let enumset = &paths.enumset;
    let internal = &paths.internal;
    let vis = &info.vis;

    let value_to_bit = if info.variants.is_empty() {
        quote! { 0 }
    } else if info.uses_lsb_encoding() {
        quote! { value as u32 }
    } else if let Some(size) = info.uses_msb_encoding() {
        quote! { ((#size as u32) - 1 - (value as u32)) }
    } else if info.uses_mask_encoding() {
        quote! { (value as i64).trailing_zeros() }
    } else {
        let variant_bits: Vec<_> = info.variants.iter().map(|x| x.variant_bit).collect();
        let variant_names: Vec<_> = info.variants.iter().map(|x| x.name.clone()).collect();
        quote! {
            match value {
                #(#name::#variant_names => #variant_bits,)*
            }
        }
    };

    let const_impls = match info.internal_repr() {
        InternalRepr::U8
        | InternalRepr::U16
        | InternalRepr::U32
        | InternalRepr::U64
        | InternalRepr::U128 => {
            quote! {
                #[automatically_derived]
                #[doc(hidden)]
                impl __EnumSetInitHelper {
                    pub const fn const_only(&self, value: #name) -> #enumset::EnumSet<#name> {
                        #internal::set::new(1 << (#value_to_bit as #repr))
                    }
                }

                #[automatically_derived]
                #[doc(hidden)]
                impl __EnumSetOpHelper {
                    pub const fn const_union(
                        &self,
                        a: #enumset::EnumSet<#name>,
                        b: #enumset::EnumSet<#name>,
                    ) -> #enumset::EnumSet<#name> {
                        #internal::set::new(#internal::set::get(a) | #internal::set::get(b))
                    }

                    pub const fn const_intersection(
                        &self,
                        a: #enumset::EnumSet<#name>,
                        b: #enumset::EnumSet<#name>,
                    ) -> #enumset::EnumSet<#name> {
                        #internal::set::new(#internal::set::get(a) & #internal::set::get(b))
                    }

                    pub const fn const_symmetric_difference(
                        &self,
                        a: #enumset::EnumSet<#name>,
                        b: #enumset::EnumSet<#name>,
                    ) -> #enumset::EnumSet<#name> {
                        #internal::set::new(#internal::set::get(a) ^ #internal::set::get(b))
                    }

                    pub const fn const_complement(
                        &self,
                        a: #enumset::EnumSet<#name>,
                    ) -> #enumset::EnumSet<#name> {
                        let all = #enumset::EnumSet::<#name>::all();
                        #internal::set::new(!#internal::set::get(a) & #internal::set::get(all))
                    }
                }
            }
        }
        InternalRepr::Array(size) => {
            quote! {
                #[automatically_derived]
                #[doc(hidden)]
                impl __EnumSetInitHelper {
                    pub const fn const_only(&self, value: #name) -> #enumset::EnumSet<#name> {
                        let mut repr = #internal::ArrayRepr::<{ #size }>([0; #size]);
                        let bit = #value_to_bit;
                        let (idx, bit) = (bit as usize / 64, bit % 64);
                        repr.0[idx] |= 1u64 << bit;
                        #internal::set::new(repr)
                    }
                }

                #[automatically_derived]
                #[doc(hidden)]
                impl __EnumSetOpHelper {
                    pub const fn const_union(
                        &self,
                        chain_a: #enumset::EnumSet<#name>,
                        chain_b: #enumset::EnumSet<#name>,
                    ) -> #enumset::EnumSet<#name> {
                        let mut a = #internal::set::get(chain_a);
                        let b = #internal::set::get(chain_b);
                        let mut i = 0;
                        while i < #size {
                            a.0[i] |= b.0[i];
                            i += 1;
                        }
                        #internal::set::new(a)
                    }

                    pub const fn const_intersection(
                        &self,
                        chain_a: #enumset::EnumSet<#name>,
                        chain_b: #enumset::EnumSet<#name>,
                    ) -> #enumset::EnumSet<#name> {
                        let mut a = #internal::set::get(chain_a);
                        let b = #internal::set::get(chain_b);
                        let mut i = 0;
                        while i < #size {
                            a.0[i] &= b.0[i];
                            i += 1;
                        }
                        #internal::set::new(a)
                    }

                    pub const fn const_symmetric_difference(
                        &self,
                        chain_a: #enumset::EnumSet<#name>,
                        chain_b: #enumset::EnumSet<#name>,
                    ) -> #enumset::EnumSet<#name> {
                        let mut a = #internal::set::get(chain_a);
                        let b = #internal::set::get(chain_b);
                        let mut i = 0;
                        while i < #size {
                            a.0[i] ^= b.0[i];
                            i += 1;
                        }
                        #internal::set::new(a)
                    }

                    pub const fn const_complement(
                        &self,
                        chain_a: #enumset::EnumSet<#name>,
                    ) -> #enumset::EnumSet<#name> {
                        let mut a = #internal::set::get(chain_a);
                        let all = #internal::set::get(#enumset::EnumSet::<#name>::all());
                        let mut i = 0;
                        while i < #size {
                            a.0[i] = !a.0[i] & all.0[i];
                            i += 1;
                        }
                        #internal::set::new(a)
                    }
                }
            }
        }
    };

    quote! {
        #[automatically_derived]
        #[doc(hidden)]
        #vis struct __EnumSetInitHelper;

        #[automatically_derived]
        #[doc(hidden)]
        #vis struct __EnumSetOpHelper;

        #const_impls

        #[automatically_derived]
        unsafe impl #internal::EnumSetConstHelper for #name {
            type ConstInitHelper = __EnumSetInitHelper;
            const CONST_INIT_HELPER: __EnumSetInitHelper = __EnumSetInitHelper;
            type ConstOpHelper = __EnumSetOpHelper;
            const CONST_OP_HELPER: __EnumSetOpHelper = __EnumSetOpHelper;
        }
    }
}
