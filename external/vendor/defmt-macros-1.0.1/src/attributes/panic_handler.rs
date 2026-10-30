use proc_macro::TokenStream;
use proc_macro_error2::{abort, abort_call_site};
use quote::quote;
use syn::{parse_macro_input, Attribute, ItemFn, ReturnType, Type};

pub(crate) fn expand(args: TokenStream, item: TokenStream) -> TokenStream {
    if !args.is_empty() {
        abort_call_site!("`#[defmt::panic_handler]` attribute takes no arguments");
    }

    let fun = parse_macro_input!(item as ItemFn);

    validate(&fun);

    codegen(&fun)
}

fn validate(fun: &ItemFn) {
    let is_divergent = match &fun.sig.output {
        ReturnType::Default => false,
        ReturnType::Type(_, ty) => matches!(&**ty, Type::Never(_)),
    };

    if fun.sig.constness.is_some()
        || fun.sig.asyncness.is_some()
        || fun.sig.unsafety.is_some()
        || fun.sig.abi.is_some()
        || !fun.sig.generics.params.is_empty()
        || fun.sig.generics.where_clause.is_some()
        || fun.sig.variadic.is_some()
        || !fun.sig.inputs.is_empty()
        || !is_divergent
    {
        abort!(fun.sig.ident, "function must have signature `fn() -> !`");
    }

    check_for_attribute_conflicts("panic_handler", &fun.attrs, &["export_name", "no_mangle"]);
}

/// Checks if any attribute in `attrs_to_check` is in `reject_list` and returns a compiler error if there's a match
///
/// The compiler error will indicate that the attribute conflicts with `attr_name`
fn check_for_attribute_conflicts(
    attr_name: &str,
    attrs_to_check: &[Attribute],
    reject_list: &[&str],
) {
    for attr in attrs_to_check {
        if let Some(ident) = attr.path().get_ident() {
            let ident = ident.to_string();

            if reject_list.contains(&ident.as_str()) {
                abort!(
                    attr,
                    "`#[{}]` attribute cannot be used together with `#[{}]`",
                    attr_name,
                    ident
                )
            }
        }
    }
}

fn codegen(fun: &ItemFn) -> TokenStream {
    let attrs = &fun.attrs;
    let block = &fun.block;
    let ident = &fun.sig.ident;

    quote!(
        #(#attrs)*
        #[export_name = "_defmt_panic"]
        #[inline(never)]
        fn #ident() -> ! {
            #block
        }
    )
    .into()
}
