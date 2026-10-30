use crate::attr::Display;
use proc_macro2::TokenStream;
use quote::quote_spanned;
use syn::{Expr, LitStr};

impl Display {
    // Transform `"error {var}"` to `"error {}", var`.
    pub(crate) fn expand_shorthand(&mut self) {
        let span = self.fmt.span();
        let fmt = self.fmt.value();
        let mut read = fmt.as_str();
        let mut out = String::new();
        let mut args = TokenStream::new();

        while let Some(brace) = read.find('{') {
            out += &read[..=brace];
            read = &read[brace + 1..];

            // skip cases where we find a {{
            if read.starts_with('{') {
                out.push('{');
                read = &read[1..];
                continue;
            }

            let close = if let Some(close) = read.find('}') {
                close
            } else {
                break;
            };

            let contents = &read[..close];
            let expr_len = contents.find(':').unwrap_or(close);

            let (expr, format) = contents.split_at(expr_len);

            let expr = if expr.starts_with(|c: char| c.is_numeric()) {
                format!("_{}", expr)
            } else {
                expr.to_string()
            };
            let expr: Expr = syn::parse_str(&expr)
                .unwrap_or_else(|e| panic!("failed to parse expression '{}': {:?}", expr, e));

            read = &read[close..];

            let arg = if cfg!(feature = "std") && format.is_empty() {
                quote_spanned!(span=> , (&(#expr)).__displaydoc_display())
            } else {
                quote_spanned!(span=> , #expr)
            };
            out.push_str(format);

            args.extend(arg);
        }

        out += read;
        self.fmt = LitStr::new(&out, self.fmt.span());
        self.args = args;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;
    use proc_macro2::Span;

    fn assert(input: &str, fmt: &str, args: &str) {
        let mut display = Display {
            fmt: LitStr::new(input, Span::call_site()),
            args: TokenStream::new(),
        };
        display.expand_shorthand();
        assert_eq!(fmt, display.fmt.value());
        assert_eq!(args, display.args.to_string());
    }

    #[test]
    fn test_expand() {
        assert("fn main() {{ }}", "fn main() {{ }}", "");
    }

    #[test]
    #[cfg_attr(not(feature = "std"), ignore)]
    fn test_std_expand() {
        assert(
            "{v} {v:?} {0} {0:?} {0.foo()} {0.foo():?}",
            "{} {:?} {} {:?} {} {:?}",
            ", (& (v)) . __displaydoc_display () , v , (& (_0)) . __displaydoc_display () , _0 , (& (_0 . foo ())) . __displaydoc_display () , _0 . foo ()",
        );
        assert(
            "error {var}",
            "error {}",
            ", (& (var)) . __displaydoc_display ()",
        );

        assert(
            "error {var1}",
            "error {}",
            ", (& (var1)) . __displaydoc_display ()",
        );

        assert(
            "error {var1var}",
            "error {}",
            ", (& (var1var)) . __displaydoc_display ()",
        );

        assert(
            "The path {0}",
            "The path {}",
            ", (& (_0)) . __displaydoc_display ()",
        );
        assert("The path {0:?}", "The path {:?}", ", _0");
    }

    #[test]
    #[cfg_attr(feature = "std", ignore)]
    fn test_nostd_expand() {
        assert(
            "{v} {v:?} {0} {0:?}",
            "{} {:?} {} {:?}",
            ", v , v , _0 , _0",
        );
        assert("error {var}", "error {}", ", var");

        assert("The path {0}", "The path {}", ", _0");
        assert("The path {0:?}", "The path {:?}", ", _0");

        assert("error {var1}", "error {}", ", var1");

        assert("error {var1var}", "error {}", ", var1var");
    }
}
