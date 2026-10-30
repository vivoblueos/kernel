use proc_macro::TokenStream;
use quote::quote;
use syn::{
    ext::IdentExt,
    parenthesized,
    parse::{discouraged::Speculative, Parse, ParseStream},
    parse_macro_input, Attribute, Expr, Ident, Token, Type, Visibility,
};

mod kw {
    use syn::custom_keyword;

    custom_keyword!(bool);
    custom_keyword!(from);
    custom_keyword!(getter);
    custom_keyword!(into);
    custom_keyword!(try_into);
    custom_keyword!(mask);
    custom_keyword!(only);
    custom_keyword!(setter);
}

// We use Bitfield in the structs/enums names to avoid confusion with the types from syn/std

struct BitfieldMask {
    ident: Ident,
    ty: Type,
}

impl Parse for BitfieldMask {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ident = input.parse()?;
        let paren_content;
        parenthesized!(paren_content in input);
        let ty = paren_content.parse()?;
        Ok(BitfieldMask { ident, ty })
    }
}

enum BitfieldPosition {
    Bit(Expr),
    MsbLsb(Expr, Expr),
    MsbLsbCount(Expr, Expr, Expr),
}

impl Parse for BitfieldPosition {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let bit_position_1 = input.parse()?;
        if !input.peek(Token!(,)) {
            return Ok(BitfieldPosition::Bit(bit_position_1));
        }
        input.parse::<Token!(,)>()?;
        let bit_position_2 = input.parse()?;
        if !input.peek(Token!(,)) {
            return Ok(BitfieldPosition::MsbLsb(bit_position_1, bit_position_2));
        }
        input.parse::<Token!(,)>()?;
        let bit_position_3 = input.parse()?;

        Ok(BitfieldPosition::MsbLsbCount(
            bit_position_1,
            bit_position_2,
            bit_position_3,
        ))
    }
}

enum FieldTy {
    Bool,
    Type(Type),
    None,
}

impl FieldTy {
    fn as_type(&self) -> Option<Type> {
        match self {
            FieldTy::Bool => Some(syn::parse_str("bool").unwrap()),
            FieldTy::Type(ty) => Some(ty.clone()),
            FieldTy::None => None,
        }
    }

    fn is_none(&self) -> bool {
        matches!(self, FieldTy::None)
    }
}

impl From<Option<Type>> for FieldTy {
    fn from(value: Option<Type>) -> Self {
        match value {
            Some(ty) => FieldTy::Type(ty),
            None => FieldTy::None,
        }
    }
}

struct BitfieldField {
    attrs: Vec<Attribute>,
    vis: Visibility,
    ty: FieldTy,
    mask: Option<BitfieldMask>,
    from: bool,
    into: bool,
    try_into: bool,
    from_into_ty: Option<Type>,
    getter: Ident,
    setter: Ident,
    bits_position: BitfieldPosition,
}

impl BitfieldField {
    fn ty_from(&self) -> Option<Type> {
        if self.from {
            self.from_into_ty.clone()
        } else {
            self.ty.as_type()
        }
    }

    fn ty_into(&self) -> Option<Type> {
        if self.into || self.try_into {
            self.from_into_ty.clone()
        } else {
            self.ty.as_type()
        }
    }
}

impl Parse for BitfieldField {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis = input.parse()?;
        let mut ty = FieldTy::None;
        if input.peek(kw::bool) && input.peek2(Token!(,)) {
            input.parse::<kw::bool>()?;
            ty = FieldTy::Bool;
            input.parse::<Token!(,)>()?;
        } else {
            let input_fork = input.fork();
            if let Ok(parsed_ty) = input_fork.parse() {
                if input_fork.peek(Token!(,)) && !input_fork.peek3(Token!(:)) {
                    ty = FieldTy::Type(parsed_ty);
                    input.advance_to(&input_fork);
                    input.parse::<Token!(,)>()?;
                }
            }
        };

        let mut mask = None;
        // We check for a comma after the keyword to differentiate the case where the keyword is in
        // fact the getter name and the normal use of the keyword.
        if input.peek(kw::mask) && !input.peek2(Token!(,)) {
            input.parse::<kw::mask>()?;
            mask = Some(input.parse()?);
            input.parse::<Token!(,)>()?;
        }

        let from = input.peek(kw::from) && !input.peek2(Token!(,));
        if from {
            input.parse::<kw::from>()?;
        }

        let into = input.peek(kw::into) && !input.peek2(Token!(,));

        let mut try_into = false;
        if into {
            input.parse::<kw::into>()?;
        } else {
            try_into = input.peek(kw::try_into) && !input.peek2(Token!(,));
            if try_into {
                input.parse::<kw::try_into>()?;
            }
        }

        let mut from_into_ty = None;
        if from || into || try_into {
            from_into_ty = Some(input.parse()?);
            input.parse::<Token!(,)>()?;
        };

        let getter = input.call(Ident::parse_any)?;
        input.parse::<Token!(,)>()?;
        let setter = input.call(Ident::parse_any)?;
        input.parse::<Token!(:)>()?;
        let bits_position = input.parse()?;

        Ok(BitfieldField {
            attrs,
            vis,
            ty,
            mask,
            from,
            into,
            try_into,
            from_into_ty,
            getter,
            setter,
            bits_position,
        })
    }
}

enum BitfieldFieldLine {
    NewDefaultType(Type),
    Field(BitfieldField),
}

impl Parse for BitfieldFieldLine {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let input_fork = input.fork();

        Ok(match input_fork.parse() {
            // check if we have a single type statement either terminated by a semicolon or the
            // end of the stream, but do not consume the semicolon
            Ok(ty) if (input_fork.is_empty() || input_fork.peek(Token!(;))) => {
                input.advance_to(&input_fork);
                BitfieldFieldLine::NewDefaultType(ty)
            }
            _ => BitfieldFieldLine::Field(input.parse()?),
        })
    }
}

struct BitfieldFieldLines(Vec<BitfieldFieldLine>);

impl BitfieldFieldLines {
    fn into_fields(self) -> Vec<BitfieldField> {
        let mut result = vec![];
        let mut default_ty = None;
        for line in self.0 {
            match line {
                BitfieldFieldLine::NewDefaultType(ty) => default_ty = Some(ty),
                BitfieldFieldLine::Field(mut field) => {
                    if field.ty.is_none() {
                        field.ty = default_ty.clone().into();
                    }
                    result.push(field)
                }
            }
        }

        result
    }
}

impl Parse for BitfieldFieldLines {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let field_lines = input
            .parse_terminated(BitfieldFieldLine::parse, Token!(;))?
            .into_iter()
            .collect();

        Ok(BitfieldFieldLines(field_lines))
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum Only {
    Getter,
    Mask,
    Setter,
    None,
}

impl Only {
    fn getter_or_none(&self) -> bool {
        *self == Only::Getter || *self == Only::None
    }

    fn mask_or_none(&self) -> bool {
        *self == Only::Mask || *self == Only::None
    }

    fn setter_or_none(&self) -> bool {
        *self == Only::Setter || *self == Only::None
    }
}

struct BitfieldFieldsWithOnly {
    only: Only,
    fields: BitfieldFieldLines,
}

impl Parse for BitfieldFieldsWithOnly {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let only = if input.peek(kw::only) {
            input.parse::<kw::only>()?;
            let only = if input.peek(kw::getter) {
                input.parse::<kw::getter>()?;
                Only::Getter
            } else if input.peek(kw::setter) {
                input.parse::<kw::setter>()?;
                Only::Setter
            } else if input.peek(kw::mask) {
                input.parse::<kw::mask>()?;
                Only::Mask
            } else {
                return Err(input
                    .error("after the only keyword, either getter, mask or setter is expected"));
            };
            input.parse::<Token!(;)>()?;
            only
        } else {
            Only::None
        };
        let fields = input.parse()?;

        Ok(BitfieldFieldsWithOnly { only, fields })
    }
}

/// Declares the fields of a struct.
///
/// This macro will generate the methods to access the fields of a bitfield. It must be called
/// from an `impl` block for a type that implements the `BitRange` and/or the `Bit` traits
/// (which traits are required depending on what type of fields are used).
///
/// The syntax of this macro is composed of declarations ended by semicolons. There are two types
/// of declarations: default type, and fields.
///
/// A default type is just a type followed by a semicolon. This will affect all the following field
/// declarations.
///
/// A field declaration is composed of the following:
///
/// * Optional attributes (`#[...]`), documentation comments (`///`) are attributes;
/// * An optional pub keyword to make the methods public
/// * An optional type followed by a comma
/// * Optionnaly, the word `mask` followed by an identifier and an type in parentheses, followed by
///   a comma
/// * Optionally, the word `from` and/or (`into` or `try_into`) followed by a type, followed by a comma
/// * The getter and setter idents, separated by a comma
/// * A colon
/// * One to three expressions of type `usize`
///
/// The attributes and pub will be applied to the two methods generated.
///
/// If the `into` part is used, the getter will convert the field after reading it.
/// If the `try_into` part is used, the getter will try to convert the field after reading it.
///
/// The getter and setter idents can be `_` to not generate one of the two. For example, if the
/// setter is `_`, the field will be read-only.
///
/// The expressions at the end are the bit positions. Their meaning depends on the number of
/// expressions:
///
///  * One expression: the field is a single bit. The type is ignored and `bool` is used. The trait
///    `Bit` is used.
///  * Two expressions: `msb, lsb`, the field is composed of the bits from `msb` to `lsb`, included.
///  * Three expressions: `msb, lsb, count`, the field is an array. The first element is composed of
///    the bits from `msb` to `lsb`. The following elements are consecutive bits range of the same
///    size.
///
/// # Example
///
/// ```ignore
/// # use bitfield_macros::bitfield_fields;
/// # fn main() {}
/// # struct FooBar(u64);
/// # bitfield_bitrange!{struct FooBar(u64)}
/// # impl From<u32> for FooBar{ fn from(_: u32) -> FooBar {unimplemented!()}}
/// # impl From<FooBar> for u32{ fn from(_: FooBar) -> u32 {unimplemented!()}}
/// # impl FooBar {
/// bitfield_fields!{
///     // The default type will be `u64
///     u64;
///     // filed1 is read-write, public, the methods are inline
///     #[inline]
///     pub field1, set_field1: 10, 0;
///     // `field2` is  read-only, private, and of type bool.
///     field2, _ : 0;
///     // `field3` will be read as an `u32` and then converted to `FooBar`.
///     // The setter is not affected, it still need an `u32` value.
///     u32, into FooBar, field3, set_field3: 10, 0;
///     // `field4` will be read as an `u32` and then converted to `FooBar`.
///     // The setter will take a `FooBar`, and converted back to an `u32`.
///     u32, from into FooBar, field4, set_field4: 10, 0;
///     // `field5` will be read as an `u32` and then converted to `FooBar`.
///     // The setter will take a `FooBar`, and converted back to an `u32`.
///     // The struct will have an associated constant `FIELD5_MASK` of type u64
///     //with the bits of field5 set
///     u32, mask FIELD5_MASK(u64), from into FooBar, field5, set_field5: 10, 0;
/// }
/// # }
/// ```
#[proc_macro]
pub fn bitfield_fields(input: TokenStream) -> TokenStream {
    let fields_with_only = parse_macro_input!(input as BitfieldFieldsWithOnly);

    let only = fields_with_only.only;
    let fields = fields_with_only.fields.into_fields();

    let getters = if only.getter_or_none() {
        generate_getters(&fields)
    } else {
        quote! {}
    };

    let setters = if only.setter_or_none() {
        generate_setters(&fields)
    } else {
        quote! {}
    };

    let masks = if only.mask_or_none() {
        generate_masks(&fields)
    } else {
        quote! {}
    };

    let expanded = quote! {
        #getters
        #setters
        #masks
    };
    TokenStream::from(expanded)
}
static MISSING_TYPE_ERROR_MESSAGE: &str =
    "For non single bit field, you need to either specify a default type or a type for each field";

fn generate_getters(fields: &[BitfieldField]) -> proc_macro2::TokenStream {
    let getters = fields.iter().flat_map(|field| {
        if field.getter != "_" {
            let attrs = &field.attrs;
            let vis = &field.vis;
            let getter = &field.getter;
            Some(match &field.bits_position {
                BitfieldPosition::Bit(bit) => {
                    quote! {
                        #(#attrs)*
                        #vis fn #getter(&self) -> bool {
                            use ::bitfield::Bit;
                            self.bit(#bit)
                         }
                    }
                }
                BitfieldPosition::MsbLsb(msb, lsb) => {
                    let ty = field.ty.as_type().expect(MISSING_TYPE_ERROR_MESSAGE);
                    let ty_into = field.ty_into().unwrap();
                    if field.try_into {
                        quote! {
                            #(#attrs)*
                            #vis fn #getter(&self) -> Result<#ty_into, <#ty_into as TryFrom<#ty>>::Error> {
                                use ::bitfield::BitRange;
                                let raw_value: #ty = self.bit_range(#msb, #lsb);
                                ::bitfield::TryInto::try_into(raw_value)
                            }
                        }
                    } else {
                        quote! {
                            #(#attrs)*
                            #vis fn #getter(&self) -> #ty_into {
                                use ::bitfield::BitRange;
                                let raw_value: #ty = self.bit_range(#msb, #lsb);
                                ::bitfield::Into::into(raw_value)
                            }
                        }
                    }
                }
                BitfieldPosition::MsbLsbCount(msb, lsb, count) => match &field.ty {
                    FieldTy::Bool => {
                        quote! {
                            #(#attrs)*
                            #vis fn #getter(&self, index: usize) -> bool {
                                use ::bitfield::Bit;
                                assert_eq!(#msb, #lsb);
                                use ::bitfield::BitRange;
                                debug_assert!(index < #count);
                                self.bit((#lsb)+index)
                            }
                        }
                    }
                    FieldTy::Type(ty) => {
                        let ty_into = field.ty_into().unwrap();
                        let (return_ty, last_line) = if field.try_into {
                            (
                                quote!{Result<#ty_into, <#ty_into as TryFrom<#ty>>::Error>}, 
                                quote!{::bitfield::TryInto::try_into(raw_value)}
                            )
                        } else {
                            (quote!{#ty_into}, quote!{::bitfield::Into::into(raw_value)})
                        };
                        quote! {
                            #(#attrs)*
                            #vis fn #getter(&self, index: usize) -> #return_ty {
                                use ::bitfield::BitRange;
                                ::bitfield::check_msb_lsb_order!(#msb, #lsb);
                                debug_assert!(index < #count);
                                #[allow(clippy::eq_op)]
                                #[allow(clippy::identity_op)]
                                let width = #msb - #lsb + 1;
                                let lsb = #lsb + index*width;
                                let msb = lsb + width - 1;
                                let raw_value: #ty = self.bit_range(msb, lsb);
                                #last_line
                            }
                        }
                    }
                    FieldTy::None => panic!("{}", MISSING_TYPE_ERROR_MESSAGE),
                },
            })
        } else {
            None
        }
    });
    quote! { #(#getters)* }
}

fn generate_setters(fields: &[BitfieldField]) -> proc_macro2::TokenStream {
    let setters = fields.iter().flat_map(|field| {
        if field.setter != "_" {
            let attrs = &field.attrs;
            let vis = &field.vis;
            let setter = &field.setter;
            Some(match &field.bits_position {
                BitfieldPosition::Bit(bit) => {
                    quote! {
                        #(#attrs)*
                        #vis fn #setter(&mut self, value: bool) {
                            use ::bitfield::BitMut;
                            self.set_bit(#bit, value);
                         }
                    }
                }
                BitfieldPosition::MsbLsb(msb, lsb) => {
                    let ty = field.ty.as_type().expect(MISSING_TYPE_ERROR_MESSAGE);
                    let ty_from = field.ty_from().unwrap();
                    quote! {
                        #(#attrs)*
                        #vis fn #setter(&mut self, value: #ty_from) {
                            use ::bitfield::BitRangeMut;
                            self.set_bit_range(#msb, #lsb, ::bitfield::Into::<#ty>::into(value));
                         }
                    }
                }
                BitfieldPosition::MsbLsbCount(msb, lsb, count) => match &field.ty {
                    FieldTy::Bool => {
                        let ty_from = field.ty_from().unwrap();
                        quote! {
                            #(#attrs)*
                            #vis fn #setter(&mut self, index: usize, value: #ty_from) {
                                use ::bitfield::BitMut;
                                debug_assert!(index < #count);;
                                self.set_bit(#lsb+index, ::bitfield::Into::<bool>::into(value));
                             }
                        }
                    }
                    FieldTy::Type(ty) => {
                        let ty_from = field.ty_from().unwrap();
                        quote! {
                            #(#attrs)*
                            #vis fn #setter(&mut self, index: usize, value: #ty_from) {
                                use ::bitfield::BitRangeMut;
                                ::bitfield::check_msb_lsb_order!(#msb, #lsb);
                                debug_assert!(index < #count);
                                #[allow(clippy::eq_op)]
                                #[allow(clippy::identity_op)]
                                let width = #msb - #lsb + 1;
                                let lsb = #lsb + index*width;
                                let msb = lsb + width - 1;
                                self.set_bit_range(msb, lsb, ::bitfield::Into::<#ty>::into(value));
                             }
                        }
                    }
                    FieldTy::None => panic!("{}", MISSING_TYPE_ERROR_MESSAGE),
                },
            })
        } else {
            None
        }
    });
    quote! { #(#setters)* }
}

fn generate_masks(fields: &[BitfieldField]) -> proc_macro2::TokenStream {
    let masks = fields.iter().flat_map(|field| {
        if let Some(mask) = &field.mask {
            let vis = &field.vis;
            let mask_ident = &mask.ident;
            let mask_ty = &mask.ty;
            Some(match &field.bits_position {
                BitfieldPosition::Bit(bit) => {
                    quote! {#vis const #mask_ident: #mask_ty = 1 << (#bit);}
                }
                BitfieldPosition::MsbLsb(msb, lsb) => {
                    quote! {
                        #vis const #mask_ident: #mask_ty = {
                            let msb = #msb;
                            let lsb = #lsb;
                            let mut i = lsb;
                            let mut acc = 0;
                            while i <= msb {
                                 acc |= 1<<i;
                                 i += 1;
                            }
                            acc
                        };
                    }
                }
                BitfieldPosition::MsbLsbCount(msb, lsb, count) => {
                    quote! {
                        #vis const #mask_ident: #mask_ty = {
                            let msb = #msb;
                            let lsb = #lsb;
                            let count = #count;
                            let width = msb - lsb;
                            let full_msb = msb + width * count;
                            let mut i = lsb;
                            let mut acc = 0;
                            while i <= full_msb {
                                acc |= 1<<i;
                                i += 1;
                            }
                            acc
                        };
                    }
                }
            })
        } else {
            None
        }
    });
    quote! { #(#masks)* }
}

/// Implements an exhaustive constructor function for a bitfield. Should only be called by `bitfield!` when using `impl new;`
#[proc_macro]
pub fn bitfield_constructor(input: TokenStream) -> TokenStream {
    let fields_with_only = parse_macro_input!(input as BitfieldFieldsWithOnly);

    let fields = fields_with_only.fields.into_fields();

    let fields_with_setter: Vec<_> = fields
        .into_iter()
        .filter(|field| field.setter != "_")
        .collect();
    let args = fields_with_setter.iter().map(|field| {
        let name = &field.setter;
        match &field.bits_position {
            BitfieldPosition::Bit(_) => {
                quote! {
                   #name: bool
                }
            }
            BitfieldPosition::MsbLsb(_, _) => {
                let ty_from = field.ty_from().expect(MISSING_TYPE_ERROR_MESSAGE);
                quote! {
                    #name: #ty_from
                }
            }
            BitfieldPosition::MsbLsbCount(_, _, _) => {
                panic!("Array fields as not supported in the `new` method generator")
            }
        }
    });

    let setter_idents = fields_with_setter.iter().map(|field| &field.setter);

    let expanded = quote! {
        #[allow(clippy::too_many_arguments, missing_docs)]
        pub fn new(#(#args,)*) -> Self {
            let mut value = Self(Default::default());
            #(value.#setter_idents(#setter_idents);)*
            value
        }
    };

    TokenStream::from(expanded)
}

struct BitfieldDebugArgs {
    name: Ident,
    field_lines: BitfieldFieldLines,
}

impl Parse for BitfieldDebugArgs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        input.parse::<Token!(struct)>()?;
        let name = input.parse()?;
        input.parse::<Token!(;)>()?;
        let field_lines = input.parse()?;

        Ok(BitfieldDebugArgs { name, field_lines })
    }
}

/// Generates a `fmt::Debug` implementation.
///
/// This macros must be called from a `impl Debug for ...` block. It will generate the `fmt` method.
///
/// In most of the case, you will not directly call this macros, but use `bitfield`.
///
/// The syntax is `struct TheNameOfTheStruct;` followed by the syntax of `bitfield_fields`.
///
/// The write-only fields are ignored.
///
/// # Example
///
/// ```ignore
/// struct FooBar(u32);
/// bitfield_bitrange!{struct FooBar(u32)}
/// impl FooBar{
///     bitfield_fields!{
///        u32;
///        field1, _: 7, 0;
///        field2, _: 31, 24;
///     }
/// }
///
/// impl std::fmt::Debug for FooBar {
///     bitfield_debug!{
///        struct FooBar;
///        field1, _: 7, 0;
///        field2, _: 31, 24;
///     }
/// }
///
/// fn main() {
///     let foobar = FooBar(0x11223344);
///     println!("{:?}", foobar);
/// }
/// ```
#[proc_macro]
pub fn bitfield_debug(input: TokenStream) -> TokenStream {
    let args = parse_macro_input!(input as BitfieldDebugArgs);

    let name = args.name;
    let fields = args.field_lines.into_fields();
    let fields_expr = fields
        .iter()
        .filter(|field| field.getter != "_")
        .map(|field| {
            let getter = &field.getter;
            match &field.bits_position {
                BitfieldPosition::Bit(_) | BitfieldPosition::MsbLsb(_, _) => {
                    quote! {
                        debug_struct.field(stringify!(#getter), &self.#getter());
                    }
                }
                BitfieldPosition::MsbLsbCount(_, _, count) => {
                    quote! {
                        let mut array = [self.#getter(0); #count];
                        for (i, e) in (&mut array).into_iter().enumerate() {
                            *e = self.#getter(i);
                        }
                        debug_struct.field(stringify!(#getter), &array);
                    }
                }
            }
        });

    let expanded = quote! {
        fn fmt(&self, f: &mut ::bitfield::fmt::Formatter) -> ::bitfield::fmt::Result {
            let mut debug_struct = f.debug_struct(stringify!(#name));
            debug_struct.field(".0", &self.0);
            #(#fields_expr)*
            debug_struct.finish()
        }
    };

    TokenStream::from(expanded)
}
