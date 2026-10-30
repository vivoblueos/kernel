/// Allows simple unit testing of proc macro implementations.
///
/// This macro only works with functions taking [`proc_macro2::TokenStream`] due
/// to the [`proc_macro`] API not being available in unit tests. This can be
/// achieved either by manually creating a separate function:
/// ```ignore
/// use proc_macro::TokenStream;
/// use proc_macro2::TokenStream as TokenStream2;
/// #[proc_macro]
/// pub fn actual_macro(input: TokenStream) -> TokenStream {
///     macro_impl(input.into()).into()
/// }
/// fn macro_impl(input: TokenStream2) -> TokenStream2 {
///     // ...
/// }
/// ```
/// or use a crate like [`manyhow`](https://docs.rs/manyhow/):
/// ```ignore
/// use proc_macro2::TokenStream as TokenStream2;
/// #[manyhow(impl_fn)] // generates `fn actual_macro_impl`
/// pub fn actual_macro(input: TokenStream2) -> TokenStream2 {
///     // ...
/// }
/// ```
///
/// # Function like macros
/// ```
/// # use proc_macro_utils::assert_expansion;
/// # use proc_macro2::TokenStream;
/// # use quote::quote;
/// // Dummy attribute macro impl
/// fn macro_impl(input: TokenStream) -> TokenStream {
///     quote!(#input)
/// }
/// fn macro_impl_result(input: TokenStream) -> Result<TokenStream, ()> {
///     Ok(quote!(#input))
/// }
/// assert_expansion!(
///     macro_impl!(something test),
///     { something test }
/// );
/// assert_expansion!(
///     macro_impl![1, 2, 3],
///     { 1, 2, 3 }
/// );
/// assert_expansion!(
///     macro_impl!{ braced },
///     { braced }
/// );
/// // adding a single function call (without arguments) is also allowed e.g. `unwrap()`
/// assert_expansion!(
///     macro_impl_result!(result).unwrap(),
///     { result }
/// );
/// ```
///
/// # Derive macros
/// ```
/// # use proc_macro_utils::assert_expansion;
/// # use proc_macro2::TokenStream;
/// # use quote::quote;
/// // Dummy derive macro impl
/// fn macro_impl(item: TokenStream) -> TokenStream {
///     quote!(#item)
/// }
/// fn macro_impl_result(item: TokenStream) -> Result<TokenStream, ()> {
///     Ok(quote!(#item))
/// }
/// assert_expansion!(
///     #[derive(macro_impl)]
///     struct A; // the comma after items is optional
///     { struct A; }
/// );
/// assert_expansion!(
///     #[derive(macro_impl)]
///     struct A {}
///     { struct A {} }
/// );
/// // adding a single function call (without arguments) is also allowed e.g. `unwrap()`
/// assert_expansion!(
///     #[derive(macro_impl_result)]
///     struct A {}.unwrap()
///     { struct A {} }
/// );
/// // alternatively the proc_macro syntax is compatible
/// assert_expansion!(
///     macro_impl!{ struct A {} },
///     { struct A {} }
/// );
/// ```
///
/// # Attribute macros
/// ```
/// # use proc_macro_utils::assert_expansion;
/// # use proc_macro2::TokenStream;
/// # use quote::quote;
/// // Dummy attribute macro impl
/// fn macro_impl(input: TokenStream, item: TokenStream) -> TokenStream {
///     quote!(#input, #item)
/// }
/// fn macro_impl_result(input: TokenStream, item: TokenStream) -> Result<TokenStream, ()> {
///     Ok(quote!(#input, #item))
/// }
/// assert_expansion!(
///     #[macro_impl]
///     struct A;
///     { , struct A; }
/// );
/// assert_expansion!(
///     #[macro_impl = "hello"]
///     fn test() { }, // the comma after items is optional
///     { "hello", fn test() {} }
/// );
/// assert_expansion!(
///     #[macro_impl(a = 10)]
///     impl Hello for World {},
///     { a = 10, impl Hello for World {} }
/// );
/// // adding a single function call (without arguments) is also allowed e.g. `unwrap()`
/// assert_expansion!(
///     #[macro_impl_result(a = 10)]
///     impl Hello for World {}.unwrap(),
///     { a = 10, impl Hello for World {} }
/// );
/// ```
///
/// # Generic usage
/// On top of the normal macro inputs a generic input is also supported.
/// ```
/// # use proc_macro_utils::assert_expansion;
/// # use proc_macro2::TokenStream;
/// # use quote::quote;
/// fn macro_impl(first: TokenStream, second: TokenStream, third: TokenStream) -> TokenStream {
///     quote!(#first, #second, #third)
/// }
/// fn macro_impl_result(first: TokenStream, second: TokenStream, third: TokenStream) -> Result<TokenStream, ()> {
///     Ok(quote!(#first, #second, #third))
/// }
/// assert_expansion!(
///     macro_impl({ 1 }, { something }, { ":)" }),
///     { 1, something, ":)" }
/// );
/// // adding a single function call (without arguments) is also allowed e.g. `unwrap()`
/// assert_expansion!(
///     macro_impl_result({ 1 }, { something }, { ":)" }).unwrap(),
///     { 1, something, ":)" }
/// );
/// ```
#[macro_export]
#[allow(clippy::module_name_repetitions)]
macro_rules! assert_expansion {
    ($macro:ident!($($input:tt)*)$(.$fn:ident())?, { $($rhs:tt)* }) => {
        $crate::assert_expansion!($macro({$($input)*})$(.$fn())?, { $($rhs)* })
    };
    ($macro:ident![$($input:tt)*]$(.$fn:ident())?, { $($rhs:tt)* }) => {
        $crate::assert_expansion!($macro({$($input)*})$(.$fn())?, { $($rhs)* })
    };
    ($macro:ident!{$($input:tt)*}$(.$fn:ident())?, { $($rhs:tt)* }) => {
        $crate::assert_expansion!($macro({$($input)*})$(.$fn())?, { $($rhs)* })
    };
    (#[derive($macro:ident)]$item:item$(.$fn:ident())?$(,)? { $($rhs:tt)* }) => {
        $crate::assert_expansion!($macro({$item})$(.$fn())?, { $($rhs)* })
    };
    (#[$macro:ident]$item:item$(.$fn:ident())?$(,)? { $($rhs:tt)* }) => {
        $crate::assert_expansion!($macro({}, {$item})$(.$fn())?, { $($rhs)* })
    };
    (#[$macro:ident = $input:expr]$item:item$(.$fn:ident())?$(,)? { $($rhs:tt)* }) => {
        $crate::assert_expansion!($macro({$input}, {$item})$(.$fn())?, { $($rhs)* })
    };
    (#[$macro:ident($($input:tt)*)]$item:item$(.$fn:ident())?$(,)? { $($rhs:tt)* }) => {
        $crate::assert_expansion!($macro({$($input)*}, {$item})$(.$fn())?, { $($rhs)* })
    };
    ($macro:ident($({$($input:tt)*}),+$(,)?)$(.$fn:ident())?, {$($rhs:tt)*}) => {
        $crate::assert_tokens!(
            $crate::__private::proc_macro2::TokenStream::from($macro(
                $(<$crate::__private::proc_macro2::TokenStream as ::core::str::FromStr>
                    ::from_str(::core::stringify!($($input)*)).unwrap().into()),+
            )$(.$fn())?),
           { $($rhs)* }
        )
    };
}

/// Asserts that the `lhs` matches the tokens wrapped in braces on the `rhs`.
///
/// `lhs` needs to be an expression implementing `IntoIterator<Item=TokenTree>`
/// e.g. [`TokenStream`](proc_macro2::TokenStream) or
/// [`TokenParser`](crate::TokenParser).
/// ```
/// # use quote::quote;
/// # use proc_macro_utils::assert_tokens;
/// let some_tokens = quote! { ident, { group } };
///
/// assert_tokens! {some_tokens, { ident, {group} }};
/// ```
#[macro_export]
#[cfg(doc)]
macro_rules! assert_tokens {
    ($lhs:expr, { $($rhs:tt)* }) => {};
}

#[macro_export]
#[cfg(not(doc))]
#[doc(hidden)]
#[allow(clippy::module_name_repetitions)]
macro_rules! assert_tokens {
    ($lhs:expr, {$($rhs:tt)*}) => {{
        let mut lhs = $crate::TokenParser::new_generic::<3, _, _>($lhs);
        $crate::assert_tokens!(@O lhs, "", $($rhs)*);
    }};
    (@E $prefix:expr, $expected:tt, $found:tt) => {
        panic!("expected\n    {}\nfound\n    {}\nat\n    {} {}", stringify!$expected, $found, $prefix, $found);
    };
    (@E $prefix:expr, $expected:tt) => {
        panic!("unexpected end, expected\n    {}\nafter\n    {}", stringify!$expected, $prefix);
    };
    (@G $lhs:ident, $fn:ident, $aggr:expr, $sym:literal, $group:tt, {$($inner:tt)*}, $($rhs:tt)*) => {
        if let Some(lhs) = $lhs.$fn() {
            let mut lhs = $crate::TokenParser::<_, 3>::from($crate::__private::proc_macro2::Group::stream(&lhs));
            $crate::assert_tokens!(@O lhs, concat!($aggr, ' ', $sym), $($inner)*);
        } else if let Some(lhs) = $lhs.next() {
            $crate::assert_tokens!(@E $aggr, ($group), lhs);
        } else {
            $crate::assert_tokens!(@E $aggr, ($group));
        }
        $crate::assert_tokens!(@O $lhs, $crate::assert_tokens!(@C $aggr, $group), $($rhs)*);
    };
    // These don't add a whitespace in front
    (@C $lhs:expr, ,) => {
        concat!($lhs, ',')
    };
    (@C $lhs:expr, :) => {
        concat!($lhs, ':')
    };
    (@C $lhs:expr, ;) => {
        concat!($lhs, ';')
    };
    (@C $lhs:expr, .) => {
        concat!($lhs, '.')
    };
    // All other tokens do
    (@C $lhs:expr, $rhs:tt) => {
        concat!($lhs, ' ', stringify!($rhs))
    };
    (@O $lhs:ident, $aggr:expr,) => { assert!($lhs.is_empty(), "unexpected left over tokens `{}`", $lhs.into_token_stream()); };
    (@O $lhs:ident, $aggr:expr, ( $($inner:tt)* ) $($rhs:tt)*) => {
        $crate::assert_tokens!(@G $lhs, next_parenthesized, $aggr, '(', { $($inner)* }, { $($inner)* }, $($rhs)*);
    };
    (@O $lhs:ident, $aggr:expr, { $($inner:tt)* } $($rhs:tt)*) => {
        $crate::assert_tokens!(@G $lhs, next_braced, $aggr, '{', { $($inner)* }, { $($inner)* }, $($rhs)*);
    };
    (@O $lhs:ident, $aggr:expr, [ $($inner:tt)* ] $($rhs:tt)*) => {
        $crate::assert_tokens!(@G $lhs, next_bracketed, $aggr, '[', [ $($inner)* ], { $($inner)* }, $($rhs)*);
    };
    (@O $lhs:ident, $aggr:expr, $token:tt $($rhs:tt)*) => {
        if let Some(lhs) = $lhs.next_macro_rules_tt().map(|t|t.to_string()).or_else(|| $lhs.next().map(|t|t.to_string())) {
            if(lhs != stringify!($token)) {
                $crate::assert_tokens!(@E $aggr, ($token), lhs);
            }
        } else {
            $crate::assert_tokens!(@E $aggr, ($token));
        }
        $crate::assert_tokens!(@O $lhs, $crate::assert_tokens!(@C $aggr, $token), $($rhs)*);
    };
}

#[test]
fn test() {
    // TODO testing with quote is incomplete `":::"` can be joint joint alone if
    // produced directly not with quote.
    use quote::quote;
    assert_tokens!(quote!(ident ident, { group/test, vec![a, (a + b)] }, "literal" $), {
        ident ident, { group /test, vec![a,(a+b)] }, "literal" $
    });
    assert_tokens!(quote!(:::), {
        :::
    });
    assert_tokens!(quote!(more:::test::test:: hello :-D $$$ It should just work), {
        more ::: test ::test:: hello :-D $$$ It should just work
    });

    assert_tokens!(quote!(:$), {: $});
}
