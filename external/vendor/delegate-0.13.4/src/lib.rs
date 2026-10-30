//! This crate removes some boilerplate for structs that simply delegate
//! some of their methods to one or more of their fields.
//!
//! It gives you the `delegate!` macro, which delegates method calls to selected expressions (usually inner fields).
//!
//! ## Features:
//! - Delegate to a method with a different name
//! ```rust
//! use delegate::delegate;
//!
//! struct Stack { inner: Vec<u32> }
//! impl Stack {
//!     delegate! {
//!         to self.inner {
//!             #[call(push)]
//!             pub fn add(&mut self, value: u32);
//!         }
//!     }
//! }
//! ```
//! - Use an arbitrary inner field expression
//! ```rust
//! use delegate::delegate;
//!
//! use std::rc::Rc;
//! use std::cell::RefCell;
//! use std::ops::Deref;
//!
//! struct Wrapper { inner: Rc<RefCell<Vec<u32>>> }
//! impl Wrapper {
//!     delegate! {
//!         to self.inner.deref().borrow_mut() {
//!             pub fn push(&mut self, val: u32);
//!         }
//!     }
//! }
//! ```
//!
//! - Delegate to enum variants
//!
//! ```rust
//! use delegate::delegate;
//!
//! enum Enum {
//!     A(A),
//!     B(B),
//!     C { v: C },
//! }
//!
//! struct A {
//!     val: usize,
//! }
//!
//! impl A {
//!     fn dbg_inner(&self) -> usize {
//!         dbg!(self.val);
//!         1
//!     }
//! }
//! struct B {
//!     val_a: String,
//! }
//!
//! impl B {
//!     fn dbg_inner(&self) -> usize {
//!         dbg!(self.val_a.clone());
//!         2
//!     }
//! }
//!
//! struct C {
//!     val_c: f64,
//! }
//!
//! impl C {
//!     fn dbg_inner(&self) -> usize {
//!         dbg!(self.val_c);
//!         3
//!     }
//! }
//!
//! impl Enum {
//!     delegate! {
//!         // transformed to
//!         //
//!         // ```rust
//!         // match self {
//!         //     Enum::A(a) => a.dbg_inner(),
//!         //     Enum::B(b) => { println!("i am b"); b }.dbg_inner(),
//!         //     Enum::C { v: c } => { c }.dbg_inner(),
//!         // }
//!         // ```
//!         to match self {
//!             Enum::A(a) => a,
//!             Enum::B(b) => { println!("i am b"); b },
//!             Enum::C { v: c } => { c },
//!         } {
//!             fn dbg_inner(&self) -> usize;
//!         }
//!     }
//! }
//! ```
//!
//! - Use modifiers that alter the generated method body
//! ```rust
//! use delegate::delegate;
//! struct Inner;
//! impl Inner {
//!     pub fn method(&self, num: u32) -> u32 { num }
//!     pub fn method_res(&self, num: u32) -> Result<u32, ()> { Ok(num) }
//! }
//! struct Wrapper { inner: Inner }
//! impl Wrapper {
//!     delegate! {
//!         to self.inner {
//!             // calls method, converts result to u64 using `From`
//!             #[into]
//!             pub fn method(&self, num: u32) -> u64;
//!
//!             // calls method, returns ()
//!             #[call(method)]
//!             pub fn method_noreturn(&self, num: u32);
//!
//!             // calls method, converts result to i6 using `TryFrom`
//!             #[try_into]
//!             #[call(method)]
//!             pub fn method2(&self, num: u32) -> Result<u16, std::num::TryFromIntError>;
//!
//!             // calls method_res, unwraps the result
//!             #[unwrap]
//!             pub fn method_res(&self, num: u32) -> u32;
//!
//!             // calls method_res, unwraps the result, then calls into
//!             #[unwrap]
//!             #[into]
//!             #[call(method_res)]
//!             pub fn method_res_into(&self, num: u32) -> u64;
//!
//!             // specify explicit type for into
//!             #[into(u64)]
//!             #[call(method)]
//!             pub fn method_into_explicit(&self, num: u32) -> u64;
//!         }
//!     }
//! }
//! ```
//!
//! - Custom called expression
//!
//! The `#[expr()]` attribute can be used to modify the delegated call. You can use the `$` sigil as a placeholder for what delegate would normally expand to, and wrap that expression with custom code.
//!
//! _Note:_ the `$` placeholder isn't required and can be present multiple times if you want.
//!
//! ```rs
//! struct A(Vec<u8>);
//!
//! impl A {
//!     delegate! {
//!         to self.0 {
//!             #[expr(*$.unwrap())]
//!             /// Here `$` == `self.0.get(idx)`
//!             /// Will expand to `*self.0.get(idx).unwrap()`
//!             fn get(&self, idx: usize) -> u8;
//!
//!             #[call(get)]
//!             #[expr($?.checked_pow(2))]
//!             /// Here `$` == `self.0.get(idx)`
//!             /// Will expand to `self.0.get(idx)?.checked_pow(2)`
//!             fn get_checked_pow_2(&self, idx: usize) -> Option<u8>;
//!         }
//!     }
//! }
//! ```
//!
//! - Call `await` on async functions
//! ```rust
//! use delegate::delegate;
//!
//! struct Inner;
//! impl Inner {
//!     pub async fn method(&self, num: u32) -> u32 { num }
//! }
//! struct Wrapper { inner: Inner }
//! impl Wrapper {
//!     delegate! {
//!         to self.inner {
//!             // calls method(num).await, returns impl Future<Output = u32>
//!             pub async fn method(&self, num: u32) -> u32;
//!
//!             // calls method(num).await.into(), returns impl Future<Output = u64>
//!             #[into]
//!             #[call(method)]
//!             pub async fn method_into(&self, num: u32) -> u64;
//!         }
//!     }
//! }
//! ```
//! You can use the `#[await(true/false)]` attribute on delegated methods to specify if `.await` should
//! be generated after the delegated expression. It will be generated by default if the delegated
//! method is `async`.
//! - Delegate to multiple fields
//! ```rust
//! use delegate::delegate;
//!
//! struct MultiStack {
//!     left: Vec<u32>,
//!     right: Vec<u32>,
//! }
//! impl MultiStack {
//!     delegate! {
//!         to self.left {
//!             // Push an item to the top of the left stack
//!             #[call(push)]
//!             pub fn push_left(&mut self, value: u32);
//!         }
//!         to self.right {
//!             // Push an item to the top of the right stack
//!             #[call(push)]
//!             pub fn push_right(&mut self, value: u32);
//!         }
//!     }
//! }
//! ```
//! - Inserts `#[inline(always)]` automatically (unless you specify `#[inline]` manually on the method)
//! - You can use an attribute on a whole segment to automatically apply it to all methods in that
//!   segment:
//! ```rust
//! use delegate::delegate;
//!
//! struct Inner;
//!
//! impl Inner {
//!   fn foo(&self) -> Result<u32, ()> { Ok(0) }
//!   fn bar(&self) -> Result<u32, ()> { Ok(1) }
//! }
//!
//! struct Wrapper { inner: Inner }
//!
//! impl Wrapper {
//!   delegate! {
//!     #[unwrap]
//!     to self.inner {
//!       fn foo(&self) -> u32; // calls self.inner.foo().unwrap()
//!       fn bar(&self) -> u32; // calls self.inner.bar().unwrap()
//!     }
//!   }
//! }
//! ```
//! - Specify expressions in the signature that will be used as delegated arguments
//! ```rust
//! use delegate::delegate;
//! struct Inner;
//! impl Inner {
//!     pub fn polynomial(&self, a: i32, x: i32, b: i32, y: i32, c: i32) -> i32 {
//!         a + x * x + b * y + c
//!     }
//! }
//! struct Wrapper { inner: Inner, a: i32, b: i32, c: i32 }
//! impl Wrapper {
//!     delegate! {
//!         to self.inner {
//!             // Calls `polynomial` on `inner` with `self.a`, `self.b` and
//!             // `self.c` passed as arguments `a`, `b`, and `c`, effectively
//!             // calling `polynomial(self.a, x, self.b, y, self.c)`.
//!             pub fn polynomial(&self, [ self.a ], x: i32, [ self.b ], y: i32, [ self.c ]) -> i32 ;
//!             // Calls `polynomial` on `inner` with `0`s passed for arguments
//!             // `a` and `x`, and `self.b` and `self.c` for `b` and `c`,
//!             // effectively calling `polynomial(0, 0, self.b, y, self.c)`.
//!             #[call(polynomial)]
//!             pub fn linear(&self, [ 0 ], [ 0 ], [ self.b ], y: i32, [ self.c ]) -> i32 ;
//!         }
//!     }
//! }
//! ```
//! - Modify how will an input parameter be passed to the delegated method with parameter attribute modifiers.
//!   Currently, the following modifiers are supported:
//!     - `#[into]`: Calls `.into()` on the parameter passed to the delegated method.
//!     - `#[as_ref]`: Calls `.as_ref()` on the parameter passed to the delegated method.
//!     - `#[newtype]`: Calls `.0` on the parameter passed to the delegated method.
//! ```rust
//! use delegate::delegate;
//!
//! struct InnerType {}
//! impl InnerType {
//!     fn foo(&self, other: Self) {}
//! }
//!
//! impl From<Wrapper> for InnerType {
//!     fn from(wrapper: Wrapper) -> Self {
//!         wrapper.0
//!     }
//! }
//!
//! struct Wrapper(InnerType);
//! impl Wrapper {
//!     delegate! {
//!         to self.0 {
//!             // Calls `self.0.foo(other.into());`
//!             pub fn foo(&self, #[into] other: Self);
//!         }
//!     }
//! }
//! ```
//! - Specify a trait through which will the delegated method be called
//!   (using [UFCS](https://doc.rust-lang.org/reference/expressions/call-expr.html#disambiguating-function-calls).
//! ```rust
//! use delegate::delegate;
//!
//! struct InnerType {}
//! impl InnerType {
//!     
//! }
//!
//! trait MyTrait {
//!   fn foo(&self);
//! }
//! impl MyTrait for InnerType {
//!   fn foo(&self) {}
//! }
//!
//! struct Wrapper(InnerType);
//! impl Wrapper {
//!     delegate! {
//!         to &self.0 {
//!             // Calls `MyTrait::foo(&self.0)`
//!             #[through(MyTrait)]
//!             pub fn foo(&self);
//!         }
//!     }
//! }
//! ```
//!
//! - Add additional arguments to method
//!
//!  ```rust
//!  use delegate::delegate;
//!  use std::cell::OnceCell;
//!  struct Inner(u32);
//!  impl Inner {
//!      pub fn new(m: u32) -> Self {
//!          // some "very complex" constructing work
//!          Self(m)
//!      }
//!      pub fn method(&self, n: u32) -> u32 {
//!          self.0 + n
//!      }
//!  }
//!  
//!  struct Wrapper {
//!      inner: OnceCell<Inner>,
//!  }
//!  
//!  impl Wrapper {
//!      pub fn new() -> Self {
//!          Self {
//!              inner: OnceCell::new(),
//!          }
//!      }
//!      fn content(&self, val: u32) -> &Inner {
//!          self.inner.get_or_init(|| Inner(val))
//!      }
//!      delegate! {
//!          to |k: u32| self.content(k) {
//!              // `wrapper.method(k, num)` will call `self.content(k).method(num)`
//!              pub fn method(&self, num: u32) -> u32;
//!          }
//!      }
//!  }
//!  ```
//! - Delegate associated functions
//!   ```rust
//!   use delegate::delegate;
//!
//!   struct A {}
//!   impl A {
//!       fn foo(a: u32) -> u32 {
//!           a + 1
//!       }
//!   }
//!
//!   struct B;
//!
//!   impl B {
//!       delegate! {
//!           to A {
//!               fn foo(a: u32) -> u32;
//!           }
//!       }
//!   }
//!
//!   assert_eq!(B::foo(1), 2);
//!   ```
//! - Delegate associated constants
//!
//! ```rust
//! use delegate::delegate;
//!
//! trait WithConst {
//!     const TOTO: u8;
//! }
//!
//! struct A;
//! impl WithConst for A {
//!     const TOTO: u8 = 1;
//! }
//!
//! struct B;
//! impl WithConst for B {
//!     const TOTO: u8 = 2;
//! }
//! struct C;
//! impl WithConst for C {
//!     const TOTO: u8 = 2;
//! }
//!
//! enum Enum {
//!     A(A),
//!     B(B),
//!     C(C),
//! }
//!
//! impl Enum {
//!     delegate! {
//!         to match self {
//!             Self::A(a) => a,
//!             Self::B(b) => b,
//!             Self::C(c) => { println!("hello from c"); c },
//!         } {
//!             #[const(WithConst::TOTO)]
//!             fn get_toto(&self) -> u8;
//!         }
//!     }
//! }
//!
//! assert_eq!(Enum::A(A).get_toto(), <A as WithConst>::TOTO);
//!
//! ```

extern crate proc_macro;
use std::mem;

use attributes::AssociatedConstant;
use proc_macro::TokenStream;

use proc_macro2::Ident;
use quote::{quote, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;
use syn::{parse_quote, Error, Expr, ExprField, ExprMethodCall, FnArg, GenericParam, Meta};

use crate::attributes::{
    combine_attributes, parse_method_attributes, parse_segment_attributes, ReturnExpression,
    SegmentAttributes,
};

mod attributes;

mod kw {
    syn::custom_keyword!(to);
    syn::custom_keyword!(target);
}

#[derive(Clone)]
enum ArgumentModifier {
    Into,
    AsRef,
    Newtype,
}

#[derive(Clone)]
enum DelegatedInput {
    Input {
        parameter: syn::FnArg,
        modifier: Option<ArgumentModifier>,
    },
    Argument(syn::Expr),
}

fn get_argument_modifier(attribute: syn::Attribute) -> Result<ArgumentModifier, Error> {
    if let Meta::Path(mut path) = attribute.meta {
        if path.segments.len() == 1 {
            let segment = path.segments.pop().unwrap();
            if segment.value().arguments.is_empty() {
                let ident = segment.value().ident.to_string();
                let ident = ident.as_str();

                match ident {
                    "into" => return Ok(ArgumentModifier::Into),
                    "as_ref" => return Ok(ArgumentModifier::AsRef),
                    "newtype" => return Ok(ArgumentModifier::Newtype),
                    _ => (),
                }
            }
        }
    };

    panic!("The attribute argument has to be `into` or `as_ref`, like this: `#[into] a: u32`.")
}

impl syn::parse::Parse for DelegatedInput {
    fn parse(input: ParseStream) -> Result<Self, Error> {
        let lookahead = input.lookahead1();
        if lookahead.peek(syn::token::Bracket) {
            let content;
            let _bracket_token = syn::bracketed!(content in input);
            let expression: syn::Expr = content.parse()?;
            Ok(Self::Argument(expression))
        } else {
            let (input, modifier) = if lookahead.peek(syn::token::Pound) {
                let mut attributes = input.call(tolerant_outer_attributes)?;
                if attributes.len() > 1 {
                    panic!("You can specify at most a single attribute for each parameter in a delegated method");
                }
                let modifier = get_argument_modifier(attributes.pop().unwrap())
                    .expect("Could not parse argument modifier attribute");

                let input: syn::FnArg = input.parse()?;
                (input, Some(modifier))
            } else {
                (input.parse()?, None)
            };

            Ok(Self::Input {
                parameter: input,
                modifier,
            })
        }
    }
}

struct DelegatedMethod {
    method: syn::TraitItemFn,
    attributes: Vec<syn::Attribute>,
    visibility: syn::Visibility,
    arguments: syn::punctuated::Punctuated<syn::Expr, syn::Token![,]>,
}

// Given an input parameter from a function signature, create a function
// argument used to call the delegate function: omit receiver, extract an
// identifier from a typed input parameter (and wrap it in an `Expr`).
fn parse_input_into_argument_expression(
    function_name: &Ident,
    input: &syn::FnArg,
) -> Option<syn::Expr> {
    match input {
        // Parse inputs of the form `x: T` to retrieve their identifiers.
        syn::FnArg::Typed(typed) => {
            match &*typed.pat {
                // This should not happen, I think. If it does,
                // it will be ignored as if it were the
                // receiver.
                syn::Pat::Ident(ident) if ident.ident == "self" => None,
                // Expression in the form `x: T`. Extract the
                // identifier, wrap it in Expr for type compatibility with bracketed expressions,
                // and append it
                // to the argument list.
                syn::Pat::Ident(ident) => {
                    let path_segment = syn::PathSegment {
                        ident: ident.ident.clone(),
                        arguments: syn::PathArguments::None,
                    };
                    let mut segments = syn::punctuated::Punctuated::new();
                    segments.push(path_segment);
                    let path = syn::Path {
                        leading_colon: None,
                        segments,
                    };
                    let ident_as_expr = syn::Expr::from(syn::ExprPath {
                        attrs: Vec::new(),
                        qself: None,
                        path,
                    });
                    Some(ident_as_expr)
                }
                // Other more complex argument expressions are not covered.
                _ => panic!(
                    "You have to use simple identifiers for delegated method parameters ({})",
                    function_name // The signature is not constructed yet. We make due.
                ),
            }
        }
        // Skip any `self`/`&self`/`&mut self` argument, since
        // it does not appear in the argument list and it's
        // already added to the parameter list.
        syn::FnArg::Receiver(_receiver) => None,
    }
}

impl syn::parse::Parse for DelegatedMethod {
    fn parse(input: ParseStream) -> Result<Self, Error> {
        let attributes = input.call(tolerant_outer_attributes)?;
        let visibility = input.call(syn::Visibility::parse)?;

        // Unchanged from Parse from TraitItemMethod
        let constness: Option<syn::Token![const]> = input.parse()?;
        let asyncness: Option<syn::Token![async]> = input.parse()?;
        let unsafety: Option<syn::Token![unsafe]> = input.parse()?;
        let abi: Option<syn::Abi> = input.parse()?;
        let fn_token: syn::Token![fn] = input.parse()?;
        let ident: Ident = input.parse()?;
        let generics: syn::Generics = input.parse()?;

        let content;
        let paren_token = syn::parenthesized!(content in input);

        // Parse inputs (method parameters) and arguments. The parameters
        // constitute the parameter list of the signature of the delegating
        // method so it must include all inputs, except bracketed expressions.
        // The argument list constitutes the list of arguments used to call the
        // delegated function. It must include all inputs, excluding the
        // receiver (self-type) input. The arguments must all be parsed to
        // retrieve the expressions inside of the brackets as well as variable
        // identifiers of ordinary inputs. The arguments must preserve the order
        // of the inputs.
        let delegated_inputs = content.parse_terminated(DelegatedInput::parse, syn::Token![,])?;
        let mut inputs: syn::punctuated::Punctuated<syn::FnArg, syn::Token![,]> =
            syn::punctuated::Punctuated::new();
        let mut arguments: syn::punctuated::Punctuated<syn::Expr, syn::Token![,]> =
            syn::punctuated::Punctuated::new();

        // First, combine the cases for pairs with cases for end, to remove
        // redundancy below.
        delegated_inputs
            .into_pairs()
            .map(|punctuated_pair| match punctuated_pair {
                syn::punctuated::Pair::Punctuated(item, comma) => (item, Some(comma)),
                syn::punctuated::Pair::End(item) => (item, None),
            })
            .for_each(|pair| match pair {
                // This input is a bracketed argument (eg. `[ self.x ]`). It
                // is omitted in the signature of the delegator, but the
                // expression inside the brackets is used in the body of the
                // delegator, as an arugnment to the delegated function (eg.
                // `self.x`). The argument needs to be generated in the
                // appropriate position with respect other arguments and non-
                // argument inputs. As long as inputs are added to the
                // `arguments` vector in order of occurance, this is trivial.
                (DelegatedInput::Argument(argument), maybe_comma) => {
                    arguments.push_value(argument);
                    if let Some(comma) = maybe_comma {
                        arguments.push_punct(comma)
                    }
                }
                // The input is a standard function parameter with a name and
                // a type (eg. `x: T`). This input needs to be reflected in
                // the delegator signature as is (eg. `x: T`). The identifier
                // also needs to be included in the argument list in part
                // (eg. `x`). The argument list needs to preserve the order of
                // the inputs with relation to arguments (see above), so the
                // parsing is best done here (previously it was done at
                // generation).
                (
                    DelegatedInput::Input {
                        parameter,
                        modifier,
                    },
                    maybe_comma,
                ) => {
                    inputs.push_value(parameter.clone());
                    if let Some(comma) = maybe_comma {
                        inputs.push_punct(comma);
                    }
                    let maybe_argument = parse_input_into_argument_expression(&ident, &parameter);
                    if let Some(mut argument) = maybe_argument {
                        let span = argument.span();

                        if let Some(modifier) = modifier {
                            let method_call = |name: &str| {
                                syn::Expr::from(ExprMethodCall {
                                    attrs: vec![],
                                    receiver: Box::new(argument.clone()),
                                    dot_token: Default::default(),
                                    method: Ident::new(name, span),
                                    turbofish: None,
                                    paren_token,
                                    args: Default::default(),
                                })
                            };

                            let field_call = || {
                                syn::Expr::from(ExprField {
                                    attrs: vec![],
                                    base: Box::new(argument.clone()),
                                    dot_token: Default::default(),
                                    member: syn::Member::Unnamed(0.into()),
                                })
                            };

                            match modifier {
                                ArgumentModifier::Into => {
                                    argument = method_call("into");
                                }
                                ArgumentModifier::AsRef => {
                                    argument = method_call("as_ref");
                                }
                                ArgumentModifier::Newtype => argument = field_call(),
                            }
                        }

                        arguments.push(argument);
                        if let Some(comma) = maybe_comma {
                            arguments.push_punct(comma);
                        }
                    }
                }
            });

        // Unchanged from Parse from TraitItemMethod
        let output: syn::ReturnType = input.parse()?;
        let where_clause: Option<syn::WhereClause> = input.parse()?;

        // This needs to be generated manually, because inputs need to be
        // separated into actual inputs that go in the signature (the
        // parameters) and the additional expressions in square brackets which
        // go into the arguments vector (artguments of the call on the method
        // on the inner object).
        let signature = syn::Signature {
            constness,
            asyncness,
            unsafety,
            abi,
            fn_token,
            ident,
            paren_token,
            inputs,
            output,
            variadic: None,
            generics: syn::Generics {
                where_clause,
                ..generics
            },
        };

        // Check if the input contains a semicolon or a brace. If it contains
        // a semicolon, we parse it (to retain token location information) and
        // continue. However, if it contains a brace, this indicates that
        // there is a default definition of the method. This is not supported,
        // so in that case we error out.
        let lookahead = input.lookahead1();
        let semi_token: Option<syn::Token![;]> = if lookahead.peek(syn::Token![;]) {
            Some(input.parse()?)
        } else {
            panic!(
                "Do not include implementation of delegated functions ({})",
                signature.ident
            );
        };

        // This needs to be populated from scratch because of the signature above.
        let method = syn::TraitItemFn {
            // All attributes are attached to `DelegatedMethod`, since they
            // presumably pertain to the process of delegation, not the
            // signature of the delegator.
            attrs: Vec::new(),
            sig: signature,
            default: None,
            semi_token,
        };

        Ok(DelegatedMethod {
            method,
            attributes,
            visibility,
            arguments,
        })
    }
}

struct DelegatedSegment {
    delegator: syn::Expr,
    methods: Vec<DelegatedMethod>,
    segment_attrs: SegmentAttributes,
}

impl syn::parse::Parse for DelegatedSegment {
    fn parse(input: ParseStream) -> Result<Self, Error> {
        let attributes = input.call(tolerant_outer_attributes)?;
        let segment_attrs = parse_segment_attributes(&attributes);

        if let Ok(keyword) = input.parse::<kw::target>() {
            return Err(Error::new(keyword.span(), "You are using the old `target` expression, which is deprecated. Please replace `target` with `to`."));
        } else {
            input.parse::<kw::to>()?;
        }

        syn::Expr::parse_without_eager_brace(input).and_then(|delegator| {
            let content;
            syn::braced!(content in input);

            let mut methods = vec![];
            while !content.is_empty() {
                methods.push(
                    content
                        .parse::<DelegatedMethod>()
                        .expect("Cannot parse delegated method"),
                );
            }

            Ok(DelegatedSegment {
                delegator,
                methods,
                segment_attrs,
            })
        })
    }
}

struct DelegationBlock {
    segments: Vec<DelegatedSegment>,
}

impl syn::parse::Parse for DelegationBlock {
    fn parse(input: ParseStream) -> Result<Self, Error> {
        let mut segments = vec![];
        while !input.is_empty() {
            segments.push(input.parse()?);
        }

        Ok(DelegationBlock { segments })
    }
}

/// Returns true if there are any `inline` attributes in the input.
fn has_inline_attribute(attrs: &[&syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if let syn::AttrStyle::Outer = attr.style {
            attr.path().is_ident("inline")
        } else {
            false
        }
    })
}

struct MatchVisitor<F>(F);

impl<F: Fn(&Expr) -> proc_macro2::TokenStream> VisitMut for MatchVisitor<F> {
    fn visit_arm_mut(&mut self, arm: &mut syn::Arm) {
        let transformed = self.0(&arm.body);
        arm.body = parse_quote!(#transformed);
    }
}

#[proc_macro]
pub fn delegate(tokens: TokenStream) -> TokenStream {
    let block: DelegationBlock = syn::parse_macro_input!(tokens);
    let sections = block.segments.iter().map(|delegator| {
        let delegated_expr = &delegator.delegator;
        let functions = delegator.methods.iter().map(|method| {
            let input = &method.method;
            let mut signature = input.sig.clone();
            if let Expr::Closure(closure) = delegated_expr {
                let additional_inputs: Vec<FnArg> = closure
                    .inputs
                    .iter()
                    .map(|input| {
                        if let syn::Pat::Type(pat_type) = input {
                            syn::parse_quote!(#pat_type)
                        } else {
                            panic!(
                                "Use a type pattern (`a: u32`) for delegation closure arguments"
                            );
                        }
                    })
                    .collect();
                let mut origin_inputs = mem::take(&mut signature.inputs).into_iter();
                // When delegating methods, `first_input` should be self or similar receivers
                // Then we need to move it to first
                // When delegating associated methods, it may be a trivial argument or does not even exist
                // We just keep the origin order.
                let first_input = origin_inputs.next();
                match first_input {
                    Some(FnArg::Receiver(receiver)) => {
                        signature.inputs.push(FnArg::Receiver(receiver));
                        signature.inputs.extend(additional_inputs);
                    }
                    Some(first_input) => {
                        signature.inputs.extend(additional_inputs);
                        signature.inputs.push(first_input);
                    }
                    _ => {
                        signature.inputs.extend(additional_inputs);
                    }
                }
                signature.inputs.extend(origin_inputs);
            }
            let attributes = parse_method_attributes(&method.attributes, input);
            let attributes = combine_attributes(attributes, &delegator.segment_attrs);
            if input.default.is_some() {
                panic!(
                    "Do not include implementation of delegated functions ({})",
                    signature.ident
                );
            }

            // Generate an argument vector from Punctuated list.
            let args: Vec<Expr> = method.arguments.clone().into_iter().collect();
            let name = match &attributes.target_method {
                Some(n) => n,
                None => &input.sig.ident,
            };
            let inline = if has_inline_attribute(&attributes.attributes) {
                quote!()
            } else {
                quote! { #[inline] }
            };
            let visibility = &method.visibility;

            let is_method = method.method.sig.receiver().is_some();
            let associated_const = &attributes.associated_constant;
            let expr_attr = &attributes.expr_attr;

            // Use the body of a closure (like `|k: u32| <body>`) as the delegation expression
            let delegated_body = if let Expr::Closure(closure) = delegated_expr {
                &closure.body
            } else {
                delegated_expr
            };

            let span = input.span();
            let generate_await = attributes
                .generate_await
                .unwrap_or_else(|| method.method.sig.asyncness.is_some());

            // fn method<'a, A, B> -> method::<A, B>
            let generic_params = &method.method.sig.generics.params;
            let generics = if generic_params.is_empty() {
                quote::quote! {}
            } else {
                let span = generic_params.span();
                let mut params: syn::punctuated::Punctuated<
                    proc_macro2::TokenStream,
                    syn::Token![,],
                > = syn::punctuated::Punctuated::new();
                for param in generic_params.iter() {
                    let token = match param {
                        GenericParam::Lifetime(_) => {
                            // Do not pass lifetimes to generic arguments explicitly to avoid
                            // things like https://doc.rust-lang.org/error_codes/E0794.html
                            // See https://github.com/Kobzol/rust-delegate/issues/85.
                            continue;
                        }
                        GenericParam::Type(t) => {
                            let token = &t.ident;
                            let span = t.span();
                            quote::quote_spanned! {span=> #token }
                        }
                        GenericParam::Const(c) => {
                            let token = &c.ident;
                            let span = c.span();
                            quote::quote_spanned! {span=> #token }
                        }
                    };
                    params.push(token);
                }
                quote::quote_spanned! {span=> ::<#params> }
            };

            let modify_expr = |expr: &Expr| {
                let body = if let Some(target_trait) = &attributes.target_trait {
                    quote::quote! { #target_trait::#name#generics(#expr, #(#args),*) }
                } else if let Some(AssociatedConstant {
                    const_name,
                    trait_path,
                }) = associated_const
                {
                    let return_type = &signature.output;
                    quote::quote! {{
                        const fn get_const<T: #trait_path>(t: &T) #return_type {
                            <T as #trait_path>::#const_name
                        }
                        get_const(#expr)
                    }}
                } else if is_method {
                    quote::quote! { #expr.#name#generics(#(#args),*) }
                } else {
                    quote::quote! { #expr::#name#generics(#(#args),*) }
                };

                let mut body = if generate_await {
                    quote::quote! { #body.await }
                } else {
                    body
                };

                for expression in &attributes.expressions {
                    match expression {
                        ReturnExpression::Into(type_name) => {
                            body = match type_name {
                                Some(name) => {
                                    quote::quote! { ::core::convert::Into::<#name>::into(#body) }
                                }
                                None => quote::quote! { ::core::convert::Into::into(#body) },
                            };
                        }
                        ReturnExpression::TryInto => {
                            body = quote::quote! { ::core::convert::TryInto::try_into(#body) };
                        }
                        ReturnExpression::Unwrap => {
                            body = quote::quote! { #body.unwrap() };
                        }
                    }
                }
                body
            };
            let mut body = if let Expr::Match(expr_match) = delegated_body {
                let mut expr_match = expr_match.clone();
                MatchVisitor(modify_expr).visit_expr_match_mut(&mut expr_match);
                expr_match.into_token_stream()
            } else {
                modify_expr(delegated_body)
            };

            if let syn::ReturnType::Default = &signature.output {
                body = quote::quote! { #body; };
            };

            if let Some(expr_template) = expr_attr {
                body = expr_template.expand_template(&body);
            }

            let attrs = &attributes.attributes;
            quote::quote_spanned! {span=>
                #(#attrs)*
                #inline
                #visibility #signature {
                    #body
                }
            }
        });

        quote! { #(#functions)* }
    });

    let result = quote! {
        #(#sections)*
    };
    result.into()
}

// we cannot use `Attributes::parse_outer` directly, because it does not allow keywords to appear
// in meta path positions, i.e., it does not accept `#[await(true)]`.
// related issue: https://github.com/dtolnay/syn/issues/1458
fn tolerant_outer_attributes(input: ParseStream) -> syn::Result<Vec<syn::Attribute>> {
    use proc_macro2::{Delimiter, TokenTree};
    use syn::{
        bracketed,
        ext::IdentExt,
        parse::discouraged::Speculative,
        token::{Brace, Bracket, Paren},
        AttrStyle, Attribute, ExprLit, Lit, MacroDelimiter, MetaList, MetaNameValue, Path, Result,
        Token,
    };

    fn tolerant_attr(input: ParseStream) -> Result<Attribute> {
        let content;
        Ok(Attribute {
            pound_token: input.parse()?,
            style: AttrStyle::Outer,
            bracket_token: bracketed!(content in input),
            meta: content.call(tolerant_meta)?,
        })
    }

    // adapted from `impl Parse for Meta`
    fn tolerant_meta(input: ParseStream) -> Result<Meta> {
        // Try to parse as Meta
        if let Ok(meta) = input.call(Meta::parse) {
            Ok(meta)
        } else {
            // If it's not possible, try to parse it as any identifier, to support #[await]
            let path = Path::from(input.call(Ident::parse_any)?);
            if input.peek(Paren) || input.peek(Bracket) || input.peek(Brace) {
                // adapted from the private `syn::attr::parse_meta_after_path`
                input.step(|cursor| {
                    if let Some((TokenTree::Group(g), rest)) = cursor.token_tree() {
                        let span = g.delim_span();
                        let delimiter = match g.delimiter() {
                            Delimiter::Parenthesis => MacroDelimiter::Paren(Paren(span)),
                            Delimiter::Brace => MacroDelimiter::Brace(Brace(span)),
                            Delimiter::Bracket => MacroDelimiter::Bracket(Bracket(span)),
                            Delimiter::None => {
                                return Err(cursor.error("expected delimiter"));
                            }
                        };
                        Ok((
                            Meta::List(MetaList {
                                path,
                                delimiter,
                                tokens: g.stream(),
                            }),
                            rest,
                        ))
                    } else {
                        Err(cursor.error("expected delimiter"))
                    }
                })
            } else if input.peek(Token![=]) {
                // adapted from the private `syn::attr::parse_meta_name_value_after_path`
                let eq_token = input.parse()?;
                let ahead = input.fork();
                let value = match ahead.parse::<Option<Lit>>()? {
                    // this branch is probably for speeding up the parsing for doc comments etc.
                    Some(lit) if ahead.is_empty() => {
                        input.advance_to(&ahead);
                        Expr::Lit(ExprLit {
                            attrs: Vec::new(),
                            lit,
                        })
                    }
                    _ => input.parse()?,
                };
                Ok(Meta::NameValue(MetaNameValue {
                    path,
                    eq_token,
                    value,
                }))
            } else {
                Ok(Meta::Path(path))
            }
        }
    }

    let mut attrs = Vec::new();
    while input.peek(Token![#]) {
        attrs.push(input.call(tolerant_attr)?);
    }
    Ok(attrs)
}
