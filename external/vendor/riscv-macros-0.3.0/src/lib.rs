use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use std::collections::HashMap;
use std::str::FromStr;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    spanned::Spanned,
    Data, DeriveInput, Ident, Token,
};

/// Struct to represent a function parameter.
struct FunctionParam {
    /// Name of the parameter.
    param_name: TokenStream2,
    /// Data type of the parameter.
    param_type: TokenStream2,
}

/// Configuration parameters of a trap. It is useful to abstract the
/// differences between exception handlers and core interrupt handlers.
struct TrapConfig {
    /// Name of the default handler (e.g., `DefaultHandler` for core interrupts).
    default_handler: TokenStream2,
    /// Vector describing all the function parameters of these kind of trap handlers.
    handler_params: Vec<FunctionParam>,
    /// Dispatch function name (e.g., `_dispatch_exception` or `_dispatch_core_interrupt`).
    dispatch_fn_name: TokenStream2,
    /// Name of the array that sorts all the trap handlers (e.g., `__CORE_INTERRUPTS`).
    handlers_array_name: TokenStream2,
}

impl TrapConfig {
    /// Vector with all the input parameters expected when declaring extern handler functions
    fn extern_signature(&self) -> Vec<TokenStream2> {
        let mut res = Vec::new();
        for param in self.handler_params.iter() {
            let param_name = &param.param_name;
            let param_type = &param.param_type;
            res.push(quote! { #param_name: #param_type });
        }
        res
    }

    /// Similar to [`Self::extern_signature`], but skipping the parameter names.
    fn array_signature(&self) -> Vec<TokenStream2> {
        let mut res = Vec::new();
        for param in self.handler_params.iter() {
            res.push(param.param_type.clone())
        }
        res
    }

    /// Similar to [`Self::extern_signature`], but skipping the parameter data types.
    fn handler_input(&self) -> Vec<TokenStream2> {
        let mut res = Vec::new();
        for param in self.handler_params.iter() {
            res.push(param.param_name.clone())
        }
        res
    }

    /// Similar to [`Self::extern_signature`], but pushing the trap `code` to the vector.
    fn dispatch_fn_signature(&self) -> Vec<TokenStream2> {
        let mut res = self.extern_signature();
        res.push(quote! {code: usize});
        res
    }
}

/// Traits that can be implemented using the `pac_enum` macro
enum PacTrait {
    Exception,
    Interrupt(InterruptType),
    Priority,
    HartId,
}

impl PacTrait {
    /// Returns a token stream representing the trait name
    fn trait_name(&self) -> TokenStream2 {
        match self {
            Self::Exception => quote!(ExceptionNumber),
            Self::Interrupt(_) => quote!(InterruptNumber),
            Self::Priority => quote!(PriorityNumber),
            Self::HartId => quote!(HartIdNumber),
        }
    }

    /// Returns a token stream representing an additional marker trait, if any.
    fn marker_trait_name(&self) -> Option<TokenStream2> {
        match self {
            Self::Interrupt(interrupt_type) => Some(interrupt_type.marker_trait_name()),
            _ => None,
        }
    }

    /// Returns a token stream representing the name of the constant that holds the maximum number
    fn const_name(&self) -> TokenStream2 {
        match self {
            Self::Exception => quote!(MAX_EXCEPTION_NUMBER),
            Self::Interrupt(_) => quote!(MAX_INTERRUPT_NUMBER),
            Self::Priority => quote!(MAX_PRIORITY_NUMBER),
            Self::HartId => quote!(MAX_HART_ID_NUMBER),
        }
    }

    /// For Exception or an Interrupt enums, it returns the trap configuration details.
    fn trap_config(&self) -> Option<TrapConfig> {
        match self {
            Self::Exception => Some(TrapConfig {
                default_handler: quote! { ExceptionHandler },
                handler_params: vec![FunctionParam {
                    param_name: quote! { trap_frame },
                    param_type: quote! { &riscv_rt::TrapFrame },
                }],
                dispatch_fn_name: quote! { _dispatch_exception },
                handlers_array_name: quote! { __EXCEPTIONS },
            }),
            Self::Interrupt(interrupt_type) => Some(TrapConfig {
                default_handler: quote! { DefaultHandler },
                handler_params: Vec::new(),
                dispatch_fn_name: interrupt_type.dispatch_fn_name(),
                handlers_array_name: interrupt_type.isr_array_name(),
            }),
            _ => None,
        }
    }
}

impl Parse for PacTrait {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        input.parse::<Token![unsafe]>()?;
        let trait_name: TokenStream2 = input.parse()?;
        match trait_name.to_string().as_str() {
            "ExceptionNumber" => Ok(Self::Exception),
            "CoreInterruptNumber" => Ok(Self::Interrupt(InterruptType::Core)),
            "ExternalInterruptNumber" => Ok(Self::Interrupt(InterruptType::External)),
            "PriorityNumber" => Ok(Self::Priority),
            "HartIdNumber" => Ok(Self::HartId),
            _ => Err(syn::Error::new(
                trait_name.span(),
                "Unknown trait name. Expected: 'ExceptionNumber', 'CoreInterruptNumber', 'ExternalInterruptNumber', 'PriorityNumber', or 'HartIdNumber'",
            )),
        }
    }
}

/// Marker traits for interrupts
enum InterruptType {
    Core,
    External,
}

impl InterruptType {
    /// Returns a token stream representing the name of the marker trait
    fn marker_trait_name(&self) -> TokenStream2 {
        match self {
            Self::Core => quote!(CoreInterruptNumber),
            Self::External => quote!(ExternalInterruptNumber),
        }
    }

    /// Returns a token stream representing the name of the array of interrupt service routines
    fn isr_array_name(&self) -> TokenStream2 {
        match self {
            Self::Core => quote!(__CORE_INTERRUPTS),
            Self::External => quote!(__EXTERNAL_INTERRUPTS),
        }
    }

    /// Returns a token stream representing the name of the interrupt dispatch function
    fn dispatch_fn_name(&self) -> TokenStream2 {
        match self {
            Self::Core => quote!(_dispatch_core_interrupt),
            Self::External => quote!(_dispatch_external_interrupt),
        }
    }
}

/// Struct containing the information needed to implement the `riscv-pac` traits for an enum
struct PacEnumItem {
    /// The name of the enum
    name: Ident,
    /// The maximum discriminant value
    max_number: usize,
    /// A map from discriminant values to variant names
    numbers: HashMap<usize, Ident>,
}

impl PacEnumItem {
    fn new(input: &DeriveInput) -> Self {
        let name = input.ident.clone();
        let (mut numbers, mut max_number) = (HashMap::new(), 0);

        let variants = match &input.data {
            Data::Enum(data) => &data.variants,
            _ => panic!("Input is not an enum"),
        };
        for v in variants.iter() {
            let ident = v.ident.clone();
            let value = match v.discriminant.as_ref() {
                Some((_, syn::Expr::Lit(expr_lit))) => match &expr_lit.lit {
                    syn::Lit::Int(lit_int) => {
                        lit_int.base10_parse::<usize>().unwrap_or_else(|_| {
                            panic!("All variant discriminants must be unsigned integers")
                        })
                    }
                    _ => panic!("All variant discriminants must be unsigned integers"),
                },
                None => panic!("Variant must have a discriminant"),
                _ => panic!("All variant discriminants must be literal expressions"),
            };

            if numbers.insert(value, ident).is_some() {
                panic!("Duplicate discriminant value");
            }
            if value > max_number {
                max_number = value;
            }
        }

        Self {
            name,
            max_number,
            numbers,
        }
    }

    /// Returns a vector of token streams representing the valid matches in the `pac::from_number` function
    fn valid_matches(&self) -> Vec<TokenStream2> {
        self.numbers
            .iter()
            .map(|(num, ident)| {
                TokenStream2::from_str(&format!("{num} => Ok(Self::{ident})")).unwrap()
            })
            .collect()
    }

    /// Returns a vector of token streams representing the interrupt handler functions
    fn handlers(&self, trap_config: &TrapConfig) -> Vec<TokenStream2> {
        let signature = trap_config.extern_signature();
        self.numbers
            .values()
            .map(|ident| {
                quote! { fn #ident (#(#signature),*) }
            })
            .collect()
    }

    /// Returns a sorted vector of token streams representing all the elements of the interrupt array.
    /// If an interrupt number is not present in the enum, the corresponding element is `None`.
    /// Otherwise, it is `Some(<interrupt_handler>)`.
    fn handlers_array(&self) -> Vec<TokenStream2> {
        let mut vectors = vec![];
        for i in 0..=self.max_number {
            if let Some(ident) = self.numbers.get(&i) {
                vectors.push(quote! { Some(#ident) });
            } else {
                vectors.push(quote! { None });
            }
        }
        vectors
    }

    fn vector_table(&self) -> TokenStream2 {
        let align = match std::env::var("RISCV_MTVEC_ALIGN") {
            Ok(x) => x.parse::<u32>().ok(),
            Err(std::env::VarError::NotPresent) => Some(4),
            Err(std::env::VarError::NotUnicode(_)) => None,
        };
        let align = match align {
            Some(x) if x.is_power_of_two() && 4 <= x => x,
            _ => {
                return quote!(compile_error!(
                    "RISCV_MTVEC_ALIGN is not a power of 2 (minimum 4)"
                ))
            }
        };
        let mut asm = format!(
            r#"
#[cfg(all(feature = "v-trap", any(target_arch = "riscv32", target_arch = "riscv64")))]
core::arch::global_asm!("
    .section .trap.vector, \"ax\"
    .global _vector_table
    .type _vector_table, @function
    
    .option push
    .balign {align}
    .option norelax
    .option norvc
    
    _vector_table:
        j _start_trap  // Interrupt 0 is used for exceptions
"#,
        );

        for i in 1..=self.max_number {
            if let Some(ident) = self.numbers.get(&i) {
                asm.push_str(&format!("        j _start_{ident}_trap\n"));
            } else {
                asm.push_str(&format!(
                    "        j _start_DefaultHandler_trap // Interrupt {i} is reserved\n"
                ));
            }
        }

        asm.push_str(
            r#"    .option pop"
);"#,
        );

        TokenStream2::from_str(&asm).unwrap()
    }

    /// Returns a vector of token streams representing the trait implementations for
    /// the enum. If the trait is an interrupt trait, the implementation also includes
    /// the interrupt handler functions and the interrupt array.
    fn impl_trait(&self, attr: &PacTrait) -> Vec<TokenStream2> {
        let mut res = vec![];

        let name = &self.name;

        let trait_name = attr.trait_name();
        let const_name = attr.const_name();

        let max_discriminant = self.max_number;
        let valid_matches = self.valid_matches();

        let is_core_interrupt = matches!(attr, PacTrait::Interrupt(InterruptType::Core));

        // Push the trait implementation
        res.push(quote! {
            unsafe impl riscv::#trait_name for #name {
                const #const_name: usize = #max_discriminant;

                #[inline]
                fn number(self) -> usize {
                    self as _
                }

                #[inline]
                fn from_number(number: usize) -> riscv::result::Result<Self> {
                    match number {
                        #(#valid_matches,)*
                        _ => Err(riscv::result::Error::InvalidVariant(number)),
                    }
                }
            }
        });

        if let Some(marker_trait_name) = attr.marker_trait_name() {
            res.push(quote! { unsafe impl riscv::#marker_trait_name for #name {} });
        }

        if let Some(trap_config) = attr.trap_config() {
            let default_handler = &trap_config.default_handler;
            let extern_signature = trap_config.extern_signature();
            let handler_input = trap_config.handler_input();
            let array_signature = trap_config.array_signature();
            let dispatch_fn_name = &trap_config.dispatch_fn_name;
            let dispatch_fn_args = &trap_config.dispatch_fn_signature();
            let vector_table = &trap_config.handlers_array_name;

            let handlers = self.handlers(&trap_config);
            let interrupt_array = self.handlers_array();
            let cfg_v_trap = match is_core_interrupt {
                true => Some(quote!(#[cfg(not(feature = "v-trap"))])),
                false => None,
            };

            // Push the interrupt handler functions and the interrupt array
            res.push(quote! {
                #cfg_v_trap
                extern "C" {
                    #(#handlers;)*
                }

                #cfg_v_trap
                #[doc(hidden)]
                #[no_mangle]
                pub static #vector_table: [Option<unsafe extern "C" fn(#(#array_signature),*)>; #max_discriminant + 1] = [
                    #(#interrupt_array),*
                ];

                #cfg_v_trap
                #[inline]
                #[no_mangle]
                unsafe extern "C" fn #dispatch_fn_name(#(#dispatch_fn_args),*) {
                    extern "C" {
                        fn #default_handler(#(#extern_signature),*);
                    }

                    match #vector_table.get(code) {
                        Some(Some(handler)) => handler(#(#handler_input),*),
                        _ => #default_handler(#(#handler_input),*),
                    }
                }
            });
        }

        if is_core_interrupt {
            res.push(self.vector_table());
        }

        res
    }
}

/// Attribute-like macro that implements the traits of the `riscv-pac` crate for a given enum.
///
/// As these traits are unsafe, the macro must be called with the `unsafe` keyword followed by the trait name.
/// In this way, we warn callers that they must comply with the requirements of the trait.
///
/// The trait name must be one of `ExceptionNumber`, `InterruptNumber`, `PriorityNumber`, or `HartIdNumber`.
/// Marker traits `CoreInterruptNumber` and `ExternalInterruptNumber` cannot be implemented using this macro.
///
/// # Safety
///
/// The struct to be implemented must comply with the requirements of the specified trait.
///
/// # Example
///
/// ```rust
/// use riscv::*;
///
/// #[repr(usize)]
/// #[pac_enum(unsafe ExceptionNumber)]
/// #[derive(Clone, Copy, Debug, Eq, PartialEq)]
/// enum Exception {
///     E1 = 1,
///     E3 = 3,
/// }
///
/// fn main() {
///     assert_eq!(Exception::E1.number(), 1);
///     assert_eq!(Exception::E3.number(), 3);
///
///     assert_eq!(Exception::from_number(1), Ok(Exception::E1));
///     assert_eq!(Exception::from_number(2), Err(2));
///     assert_eq!(Exception::from_number(3), Ok(Exception::E3));
///
///     assert_eq!(Exception::MAX_EXCEPTION_NUMBER, 3);
/// }
///```
#[proc_macro_attribute]
pub fn pac_enum(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    let pac_enum = PacEnumItem::new(&input);

    let attr = parse_macro_input!(attr as PacTrait);

    let trait_impl = pac_enum.impl_trait(&attr);
    quote! {
        #input
        #(#trait_impl)*
    }
    .into()
}
