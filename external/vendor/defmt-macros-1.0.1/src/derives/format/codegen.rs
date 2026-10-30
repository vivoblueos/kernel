use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{DataStruct, Ident, ImplGenerics, TypeGenerics, WhereClause, WherePredicate};

pub(crate) use enum_data::encode as encode_enum_data;

use crate::construct;

mod enum_data;
mod fields;

pub(crate) struct EncodeData {
    pub(crate) format_tag: TokenStream2,
    pub(crate) stmts: Vec<TokenStream2>,
    pub(crate) where_predicates: Vec<WherePredicate>,
}

pub(crate) fn encode_struct_data(
    ident: &Ident,
    data: &DataStruct,
    defmt_path: &syn::Path,
) -> syn::Result<EncodeData> {
    let mut format_string = ident.to_string();
    let mut stmts = vec![];
    let mut field_patterns = vec![];

    let (encode_fields_stmts, where_predicates) = fields::codegen(
        &data.fields,
        &mut format_string,
        &mut field_patterns,
        defmt_path,
    )?;

    stmts.push(quote!(match self {
        Self { #(#field_patterns),* } => {
            #(#encode_fields_stmts;)*
        }
    }));

    let format_tag = construct::interned_string(&format_string, "derived", false, None, defmt_path);
    Ok(EncodeData {
        format_tag,
        stmts,
        where_predicates,
    })
}

pub(crate) struct Generics<'a> {
    pub(crate) impl_generics: ImplGenerics<'a>,
    pub(crate) type_generics: TypeGenerics<'a>,
    pub(crate) where_clause: WhereClause,
}

impl<'a> Generics<'a> {
    pub(crate) fn codegen(
        generics: &'a mut syn::Generics,
        where_predicates: Vec<WherePredicate>,
    ) -> Self {
        let mut where_clause = generics.make_where_clause().clone();
        let (impl_generics, type_generics, _) = generics.split_for_impl();

        // Extend where-clause with `Format` bounds for all field types.
        where_clause.predicates.extend(where_predicates);

        Self {
            impl_generics,
            type_generics,
            where_clause,
        }
    }
}
