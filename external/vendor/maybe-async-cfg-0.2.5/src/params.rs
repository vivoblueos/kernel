use std::collections::HashMap;
#[allow(unused_imports)]
use std::iter::FromIterator;

use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, ToTokens};
use syn::{
    punctuated::Punctuated, spanned::Spanned, token::Comma, Attribute, AttributeArgs, Ident, Lit,
    LitStr, Meta, MetaNameValue, NestedMeta, MetaList, 
};

use crate::{
    DEFAULT_CRATE_NAME, STANDARD_MACROS,
    utils::*,
};

const MODE_INTO_ASYNC: &'static str = "__into_async";
const MODE_INTO_SYNC: &'static str = "__into_sync";

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, Copy)]
pub enum ConvertMode {
    IntoSync,
    IntoAsync,
}

impl ConvertMode {
    fn from_str<S: AsRef<str>>(s: S) -> Option<Self> {
        match s.as_ref() {
            "sync" => Some(Self::IntoSync),
            "async" => Some(Self::IntoAsync),
            _ => None,
        }
    }

    fn to_str(&self) -> &'static str {
        match self {
            Self::IntoSync => "sync",
            Self::IntoAsync => "async",
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub struct IdentRecord {
    pub snake_case: bool,
    pub use_mode: bool,
    pub keep: bool,
    pub ident_sync: Option<String>,
    pub ident_async: Option<String>,
    pub idents: Option<HashMap<String, String>>,
}

impl IdentRecord {
    pub fn new() -> Self {
        Self {
            snake_case: false,
            use_mode: false,
            keep: false,
            ident_sync: None,
            ident_async: None,
            idents: None,
        }
    }

    pub fn with_snake_case( snake_case: bool ) -> Self {
        Self {
            snake_case,
            use_mode: false,
            keep: false,
            ident_sync: None,
            ident_async: None,
            idents: None,
        }
    }

    pub fn ident_add_suffix(&self, ident: &Ident, convert_mode: ConvertMode, version_name: Option<&str>) -> Ident {
        if self.keep {
            return ident.clone();
        }

        if let Some(version_name) = version_name {
            if let Some(idents) = self.idents.as_ref() {
                if let Some(value) = idents.get(version_name) {
                    return Ident::new(value, ident.span());
                }
            }
        }

        match convert_mode {
            ConvertMode::IntoSync => {
                if let Some(name) = &self.ident_sync {
                    return Ident::new(&name, ident.span());
                }
            }
            ConvertMode::IntoAsync => {
                if let Some(name) = &self.ident_async {
                    return Ident::new(&name, ident.span());
                }
            }
        };

        let suffix = match (self.snake_case, convert_mode) {
            (false, ConvertMode::IntoAsync) => "Async",
            (false, ConvertMode::IntoSync) => "Sync",
            (true, ConvertMode::IntoAsync) => "_async",
            (true, ConvertMode::IntoSync) => "_sync",
        };

        Ident::new(&format!("{}{}", ident, suffix), ident.span())
    }

    pub fn to_nestedmeta(&self, name: &str) -> syn::NestedMeta {
        let mut nested = Punctuated::<syn::NestedMeta, syn::token::Comma>::new();
        
        if self.snake_case {
            nested.push(syn::NestedMeta::Meta(syn::Meta::Path(make_path("snake"))));
        };
    
        if self.use_mode {
            nested.push(syn::NestedMeta::Meta(syn::Meta::Path(make_path("use"))));
        };
    
        if self.keep {
            nested.push(syn::NestedMeta::Meta(syn::Meta::Path(make_path("keep"))));
        };
    
        if let Some(value) = &self.ident_async {
            if value == name {
                nested.push(syn::NestedMeta::Meta(syn::Meta::Path(make_path("async"))));
            } else {
                nested.push(make_nestedmeta_namevalue("async", value.as_str()));
            }
        };
        if let Some(value) = &self.ident_sync {
            if value == name {
                nested.push(syn::NestedMeta::Meta(syn::Meta::Path(make_path("sync"))));
            } else {
                nested.push(make_nestedmeta_namevalue("sync", value.as_str()));
            }
        };
    
        if let Some(idents) = &self.idents {
            for (key, value) in idents {
                nested.push(make_nestedmeta_namevalue(key.as_str(), value.as_str()));
            }
        };
    
        if nested.is_empty() {
            syn::NestedMeta::Meta(syn::Meta::Path(make_path(name)))
        } else {
            make_nestedmeta_list(name, nested)
        }
    }    
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub struct MacroParameterVersion {
    pub kind: ConvertMode,
    pub params: MacroParameters,
}

#[derive(Clone)]
pub struct MacroParameters {
    mode: Option<ConvertMode>,
    disable: bool,
    key: Option<String>,
    self_name: Option<String>,
    keep_self: bool,
    // settings
    prefix: Option<String>,
    idents: HashMap<String, IdentRecord>,
    send: Option<bool>,
    recursive_asyncness_removal: bool,
    // groups
    cfg: Option<Meta>,
    outer_attrs: Punctuated<NestedMeta, Comma>,
    inner_attrs: Punctuated<NestedMeta, Comma>,
    drop_attrs: Vec<String>,
    replace_features: HashMap<String, String>,
    // versions
    pub versions: Vec<MacroParameterVersion>,
}

impl std::fmt::Debug for MacroParameters {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {    
        f.debug_struct("MacroParameters")
           .field("mode", &self.mode)
           .field("disable", &self.disable)
           .field("key", &self.key)
           .field("self_name", &self.self_name)
           .field("prefix", &self.prefix)
           .field("idents", &self.idents)
           .field("send", &self.send)
           .field("recursive_asyncness_removal", &self.recursive_asyncness_removal)
           .field("keep_self", &self.keep_self)
           .field("cfg", &OptionToTokens(self.cfg.as_ref()))
           .field("outer_attrs", &DebugByDisplay(self.outer_attrs.to_token_stream()))
           .field("inner_attrs", &DebugByDisplay(self.inner_attrs.to_token_stream()))
           .field("outer_attrs", &DebugByDisplay(self.outer_attrs.to_token_stream()))
           .field("drop_attrs", &self.drop_attrs)
           .field("replace_features", &self.replace_features)
           .field("versions", &self.versions)
           .finish()
        }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

macro_rules! lit_str {
    ($lit:ident, $obj:expr, $fn:ident, $msg:expr) => {
        match $lit {
            syn::Lit::Str(str_val) => $obj.$fn(str_val.value())?,
            _ => return Err(syn::Error::new_spanned($lit.to_token_stream(), $msg)),
        }
    };
}

macro_rules! lit_meta {
    ($lit:ident, $meta:expr, $obj:expr, $fn:ident, $msg:expr) => {
        match $lit {
            syn::Lit::Str(_) => $obj.$fn($meta)?,
            _ => return Err(syn::Error::new_spanned($lit.to_token_stream(), $msg)),
        }
    };
}

impl MacroParameters {
    #[allow(dead_code)]
    pub fn new() -> Self {
        MacroParametersBuilder::new().build().unwrap()
    }

    fn from_args<'i>(args: impl IntoIterator<Item = &'i NestedMeta>) -> syn::Result<Self> {
        let mut builder = MacroParametersBuilder::new();

        for arg in args {
            match arg {
                syn::NestedMeta::Meta(meta) => match meta {
                    syn::Meta::NameValue(syn::MetaNameValue { path, lit, .. }) => {
                        let name = path
                            .get_ident()
                            .ok_or(syn::Error::new_spanned(
                                path.to_token_stream(),
                                "Expected name",
                            ))?
                            .to_string();
                        match name.as_str() {
                            "key" => lit_str!(lit, builder, key, "Expected string literal"),
                            "self" => lit_str!(lit, builder, self_name, "Expected string literal"),
                            "prefix" => lit_str!(lit, builder, prefix, "Expected string literal"),
                            "send" => lit_str!(lit, builder, send, "Expected string literal"),
                            "feature" => lit_meta!(lit, meta, builder, feature, "Expected string literal"),
                            _ => {
                                return Err(syn::Error::new_spanned(
                                    meta.to_token_stream(),
                                    format!("Wrong name for name-value pair: {}", &name),
                                ))
                            }
                        }
                    }
                    syn::Meta::List(list) => {
                        let name = list
                            .path
                            .get_ident()
                            .ok_or(syn::Error::new_spanned(
                                list.path.to_token_stream(),
                                "Expected name",
                            ))?
                            .to_string();
                        match name.as_str() {
                            "cfg" => builder.cfg_list(list)?,
                            "idents" => MacroParametersBuilder::idents(
                                &mut builder.params.idents,
                                &list.nested,
                            )?,
                            "any" | "all" | "not" => builder.cfg_meta(meta)?,
                            "outer" => builder.outer_attrs(&list.nested)?,
                            "inner" => builder.inner_attrs(&list.nested)?,
                            "replace_feature" => builder.replace_feature(&list.nested)?,
                            "drop_attrs" => builder.drop_attrs(&list.nested)?,
                            name @ _ => builder.version_or_inner_attr(name, &list.nested, meta)?,
                        }
                    }
                    syn::Meta::Path(path) => {
                        if let Some(name) = path.get_ident().map(|i| i.to_string()) {
                            match name.as_str() {
                                MODE_INTO_ASYNC => builder.mode_into_async()?,
                                MODE_INTO_SYNC => builder.mode_into_sync()?,
                                "disable" => builder.disable(),
                                "keep_self" => builder.keep_self(),
                                _ => builder.inner_attr(meta)?,
                            }
                        } else {
                            builder.inner_attr(meta)?    
                        }
                    }
                },
                syn::NestedMeta::Lit(lit) => {
                    lit_meta!(lit, lit, builder, inner_attr_str, "Expected string literal")
                }
            }
        }

        builder.build()
    }

    pub fn from_tokens(tokens: TokenStream) -> syn::Result<Self> {
        let args = match syn::parse_macro_input::parse::<AttributeArgs>(tokens) {
            Ok(a) => a,
            Err(e) => return Err(e),
        };

        Self::from_args(&args)
    }

    pub fn from_tokens_in_parens(tokens: TokenStream) -> syn::Result<Self> {
        let aip = match syn::parse_macro_input::parse::<AttributeArgsInParens>(tokens) {
            Ok(a) => a,
            Err(e) => {
                return Err(e);
            }
        };

        Self::from_args(&aip.args)
    }

    pub fn to_nestedmeta(&self, add_mode: Option<ConvertMode>) -> Punctuated<syn::NestedMeta, syn::token::Comma> {
        let mut args = Punctuated::<syn::NestedMeta, syn::token::Comma>::new();

        let mode = if let Some(mode) = add_mode { 
            Some(mode)
        } else if let Some(mode) = self.mode {
            Some(mode)
        } else {
            None
        };
        
        if let Some(mode) = mode { 
            match mode {
                ConvertMode::IntoAsync => args.push(NestedMeta::Meta(Meta::Path(make_path(MODE_INTO_ASYNC)))),
                ConvertMode::IntoSync => args.push(NestedMeta::Meta(Meta::Path(make_path(MODE_INTO_SYNC)))),
            }
        }

        if self.disable {
            args.push(NestedMeta::Meta(Meta::Path(make_path("disable"))));
        }

        if self.keep_self {
            args.push(NestedMeta::Meta(Meta::Path(make_path("keep_self"))));
        }

        if let Some(key) = &self.key {
            args.push(make_nestedmeta_namevalue("key", key.as_str()));
        }

        if let Some(self_name) = &self.self_name {
            args.push(make_nestedmeta_namevalue("self", self_name.as_str()));
        }

        if let Some(prefix) = &self.prefix {
            args.push(make_nestedmeta_namevalue("prefix", prefix.as_str()));
        }

        if let Some(send) = &self.send {
            args.push(make_nestedmeta_namevalue(
                "prefix",
                if *send { "Send" } else { "?Send" },
            ));
        }

        if let Some(cfg) = &self.cfg {
            let mut nested = Punctuated::new();
            nested.push(NestedMeta::Meta(cfg.clone()));
            args.push(make_nestedmeta_list("cfg", nested));
        }

        if !self.outer_attrs.is_empty() {
            args.push(make_nestedmeta_list("outer", self.outer_attrs.clone()));
        }

        if !self.inner_attrs.is_empty() {
            args.push(make_nestedmeta_list("inner", self.inner_attrs.clone()));
        }

        if !self.idents.is_empty() {
            let mut nested = Punctuated::<syn::NestedMeta, syn::token::Comma>::new();
            for (name, value) in &self.idents {
                nested.push(value.to_nestedmeta(name.as_str()));
            }
            let arg = make_nestedmeta_list("idents", nested);
            args.push(arg);
        }

        if !self.drop_attrs.is_empty() {
            let mut nested = Punctuated::<syn::NestedMeta, syn::token::Comma>::new();
            for name in &self.drop_attrs {
                nested.push(NestedMeta::Meta(Meta::Path(make_path(name.as_str()))));
            }
            let arg = make_nestedmeta_list("drop_attrs", nested);
            args.push(arg);
        }

        if !self.replace_features.is_empty() {
            for (name, value) in &self.replace_features {
                let mut inner = Punctuated::<syn::NestedMeta, syn::token::Comma>::new();
                inner.push(NestedMeta::Lit(Lit::Str(LitStr::new(
                    name.as_str(),
                    Span::call_site(),
                ))));
                inner.push(NestedMeta::Lit(Lit::Str(LitStr::new(
                    value.as_str(),
                    Span::call_site(),
                ))));
                let arg = make_nestedmeta_list("replace_feature", inner);
                args.push(arg);
            }
        }

        for version in &self.versions {
            let (name, nested) = match version.kind {
                ConvertMode::IntoSync | ConvertMode::IntoAsync => {
                    (version.kind.to_str(), version.params.to_nestedmeta(None))
                }
            };

            let arg = make_nestedmeta_list(name, nested);
            args.push(arg);
        }

        args
    }

    pub fn extend_tokenstream2_with_cfg_outer_attrs(
        &self,
        ts: &mut TokenStream2,
    ) -> syn::Result<()> {
        if let Some(cfg_cond) = &self.cfg {
            let cfg_ts = cfg_cond.into_token_stream();
            ts.extend(quote!(#[cfg(#cfg_ts)]));
        };

        for attr in &self.outer_attrs {
            match attr {
                NestedMeta::Meta(_) => {
                    let attr_ts = attr.into_token_stream();
                    ts.extend(quote!(#[#attr_ts]));
                }
                NestedMeta::Lit(syn::Lit::Str(s)) => {
                    let attr_ts = make_attr_ts_from_str(s.value(), attr.span())?;
                    ts.extend(attr_ts);
                }
                _ => {
                    unreachable!()
                }
            };
        }

        Ok(())
    }

    pub fn extend_tokenstream2_with_inner_attrs(&self, ts: &mut TokenStream2) -> syn::Result<()> {
        for attr in &self.inner_attrs {
            match attr {
                NestedMeta::Meta(_) => {
                    let attr_ts = attr.into_token_stream();
                    ts.extend(quote!(#[#attr_ts]));
                }
                NestedMeta::Lit(syn::Lit::Str(s)) => {
                    let attr_ts = make_attr_ts_from_str(s.value(), attr.span())?;
                    ts.extend(attr_ts);
                }
                _ => {
                    unreachable!()
                }
            };
        }

        Ok(())
    }

    pub fn to_tokens(&self, add_mode: Option<ConvertMode>) -> TokenStream2 {
        self.to_nestedmeta(add_mode).to_token_stream()
    }

    pub fn default_ident_record(&self, snake_case: bool) -> IdentRecord {
        IdentRecord::with_snake_case( snake_case )
    }

    pub fn apply_parent(child: &mut MacroParameters, parent: &MacroParameters) -> syn::Result<()> {
        if parent.disable {
            child.disable = true;
        }

        if parent.keep_self {
            child.keep_self = true;
        }

        if !parent.idents.is_empty() {
            child.idents.extend(parent.idents.clone());
        }

        if !parent.drop_attrs.is_empty() {
            let mut new_drop_attrs = parent.drop_attrs.clone();
            new_drop_attrs.extend_from_slice(&child.drop_attrs);
            child.drop_attrs = new_drop_attrs;
        }

        if !parent.replace_features.is_empty() {
            child
                .replace_features
                .extend(parent.replace_features.clone());
        }

        Ok(())
    }

    pub fn disable_get(&self) -> bool {
        self.disable
    }

    pub fn mode_get(&self) -> Option<ConvertMode> {
        self.mode
    }

    pub fn key_get<'s>(&'s self) -> Option<&'s str> {
        self.key.as_ref().map(|s| s.as_str())
    }

    pub fn original_self_name_set<S: AsRef<str>>(&mut self, name: S, snake_case: bool) {
        if !self.keep_self {
            if self.idents.get(name.as_ref()).is_none() {
                let mut ir = self.default_ident_record(snake_case);
    
                if let Some(key) = &self.key {
                    if let Some(self_name) = &self.self_name {
                        let mut idents = HashMap::new();
                        idents.insert( key.clone(), self_name.clone() );
                        ir.idents = Some(idents);
                    }
                }
    
                self.idents.insert(name.as_ref().to_string(), ir);
            }
        }
    }

    pub fn prefix_set(&mut self, prefix: String) {
        self.prefix = Some(prefix);
    }

    pub fn prefix_get(&self) -> &str {
        self.prefix
            .as_ref()
            .map(|s| s.as_str())
            .unwrap_or(DEFAULT_CRATE_NAME)
    }

    pub fn send_get(&self) -> Option<bool> {
        self.send
    }

    pub fn recursive_asyncness_removal_get(&self) -> bool {
        self.recursive_asyncness_removal
    }

    pub fn idents_get<'s, S: AsRef<str>>(&'s self, name: S) -> Option<&'s IdentRecord> {
        self.idents.get(name.as_ref())
    }

    pub fn replace_features_is_empty(&self) -> bool {
        self.replace_features.is_empty()
    }
    pub fn replace_features_get<'s, S: AsRef<str>>(&'s self, name: S) -> Option<&'s str> {
        self.replace_features.get(name.as_ref()).map(|s| s.as_str())
    }

    pub fn drop_attrs_is_empty(&self) -> bool {
        self.drop_attrs.is_empty()
    }
    pub fn drop_attrs_contains(&self, name: &String) -> bool {
        self.drop_attrs.contains(name)
    }

    pub fn is_our_attr(&self, attr: &Attribute) -> Option<String> {
        if attr.style == syn::AttrStyle::Outer {
            if attr.path.leading_colon.is_none() && attr.path.segments.len() == 2 {
                let first_segment = &attr.path.segments[0];
                let last_segment = &attr.path.segments[1];
                if first_segment.arguments == syn::PathArguments::None
                    && last_segment.arguments == syn::PathArguments::None
                {
                    let first = first_segment.ident.to_string();
                    let last = last_segment.ident.to_string();

                    if let Some(prefix) = &self.prefix {
                        if &first == prefix {
                            return Some(last);
                        }
                    } else {
                        return Some(last);
                    }
                }
            }
        };

        None
    }

    pub fn make_self_path(&self, name: &str) -> syn::Path {
        let mut segments = Punctuated::<syn::PathSegment, syn::token::Colon2>::new();
        segments.push_value(syn::PathSegment {
            ident: Ident::new(
                self.prefix
                    .as_ref()
                    .map(|s| s.as_str())
                    .unwrap_or(self.prefix_get()),
                Span::call_site(),
            ),
            arguments: syn::PathArguments::None,
        });
        segments.push_punct(syn::Token![::](Span::call_site()));
        segments.push_value(syn::PathSegment {
            ident: Ident::new(name, Span::call_site()),
            arguments: syn::PathArguments::None,
        });

        syn::Path {
            leading_colon: None,
            segments,
        }
    }

    pub fn standard_macros<'s>(&'s self) -> &[&'s str] {
        STANDARD_MACROS
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub struct MacroParametersBuilder {
    params: MacroParameters,
}

impl MacroParametersBuilder {
    pub fn new() -> Self {
        Self {
            params: MacroParameters {
                mode: None,
                disable: false,
                key: None,
                self_name: None, 
                prefix: None,
                idents: HashMap::new(),
                keep_self: false,
                send: None,
                recursive_asyncness_removal: true,
                cfg: None,
                outer_attrs: Punctuated::new(),
                inner_attrs: Punctuated::new(),
                drop_attrs: vec![],
                replace_features: HashMap::new(),
                versions: vec![],
            },
        }
    }

    pub fn mode_into_sync(&mut self) -> syn::Result<()> {
        self.params.mode = Some(ConvertMode::IntoSync);
        Ok(())
    }

    pub fn mode_into_async(&mut self) -> syn::Result<()> {
        self.params.mode = Some(ConvertMode::IntoAsync);
        Ok(())
    }

    pub fn key(&mut self, key: String) -> syn::Result<()> {
        self.params.key = Some(key);
        Ok(())
    }

    pub fn self_name(&mut self, self_name: String) -> syn::Result<()> {
        self.params.self_name = Some(self_name);
        Ok(())
    }

    pub fn disable(&mut self) {
        self.params.disable = true;
    }

    pub fn keep_self(&mut self) {
        self.params.keep_self = true;
    }

    pub fn prefix(&mut self, prefix: String) -> syn::Result<()> {
        self.params.prefix = Some(prefix);
        Ok(())
    }

    pub fn idents(
        idents: &mut HashMap<String, IdentRecord>,
        list: &Punctuated<NestedMeta, Comma>,
    ) -> syn::Result<()> {
        for nm in list {
            match nm {
                NestedMeta::Meta(Meta::Path(path)) => {
                    let ident = path
                        .get_ident()
                        .ok_or(syn::Error::new_spanned(
                            nm.to_token_stream(),
                            "Expected ident, but not complex path",
                        ))?
                        .to_string();
                    let ir = IdentRecord::new();
                    idents.insert(ident, ir);
                }
                NestedMeta::Meta(Meta::List(syn::MetaList { path, nested, .. })) => {
                    let ident = path
                        .get_ident()
                        .ok_or(syn::Error::new_spanned(
                            nm.to_token_stream(),
                            "Expected ident, but not complex path",
                        ))?
                        .to_string();
                    let mut ir = IdentRecord::new();
                    for inm in nested {
                        match inm {
                            NestedMeta::Meta(Meta::Path(path)) => {
                                let iname = path
                                    .get_ident()
                                    .ok_or(syn::Error::new_spanned(
                                        nm.to_token_stream(),
                                        "Expected ident, but not complex path",
                                    ))?
                                    .to_string();
                                match iname.as_str() {
                                    "snake" | "fn" | "mod" => {
                                        ir.snake_case = true;
                                    }
                                    "use" => {
                                        ir.use_mode = true;
                                    }
                                    "keep" => {
                                        ir.keep = true;
                                    }
                                    "sync" => {
                                        ir.ident_sync = Some(ident.clone());
                                    }
                                    "async" => {
                                        ir.ident_async = Some(ident.clone());
                                    }
                                    _ => {
                                        return Err(syn::Error::new_spanned(
                                            nm.to_token_stream(),
                                            "Expected snake, fn, mod, use, keep, sync, async",
                                        ))
                                    }
                                }
                            }
                            NestedMeta::Meta(Meta::NameValue(MetaNameValue {
                                path,
                                lit: syn::Lit::Str(lit),
                                ..
                            })) => {
                                let iname = path
                                    .get_ident()
                                    .ok_or(syn::Error::new_spanned(
                                        nm.to_token_stream(),
                                        "Expected ident, but not complex path",
                                    ))?
                                    .to_string();
                                let ivalue = lit.value();
                                match iname.as_str() {
                                    "sync" => {
                                        ir.ident_sync = Some(ivalue);
                                    }
                                    "async" => {
                                        ir.ident_async = Some(ivalue);
                                    }
                                    _ => {
                                        let idents = ir.idents.get_or_insert_with(|| HashMap::new());
                                        idents.insert(iname, ivalue);
                                    }
                                }
                            }
                            _ => {
                                return Err(syn::Error::new_spanned(
                                    nm.to_token_stream(),
                                    "Expected fn, sync = \"ident\", or async = \"ident\"",
                                ))
                            }
                        }
                    }
                    idents.insert(ident, ir);
                }
                _ => {
                    return Err(syn::Error::new_spanned(
                        nm.to_token_stream(),
                        "Expected name = \"value\" pair",
                    ))
                }
            }
        }

        Ok(())
    }

    pub fn send(&mut self, send: String) -> syn::Result<()> {
        self.params.send = Some(match send.as_str() {
            "" | "Send" | "true" => true,
            "?Send" | "false" => false,
            _ => {
                return Err(syn::Error::new(
                    Span::call_site(),
                    "Only accepts `Send` or `?Send`",
                ));
            }
        });

        Ok(())
    }

    pub fn feature(&mut self, meta: &Meta) -> syn::Result<()> {
        self.cfg_meta(meta)
    }

    pub fn cfg_list(&mut self, list: &MetaList) -> syn::Result<()> {
        match list.nested.len() {
            0 => {
                return Err(syn::Error::new_spanned(
                    list.to_token_stream(),
                    "Expected condition",
                ))
            }
            1 => {
                let first = list.nested.first().unwrap();
                match first {
                    NestedMeta::Meta(first_meta) => self.cfg_meta(first_meta)?,
                    _ => {
                        return Err(syn::Error::new_spanned(
                            list.to_token_stream(),
                            "Expected condition",
                        ))
                    }
                }
            }
            _ => {
                return Err(syn::Error::new_spanned(
                    list.to_token_stream(),
                    "Expected condition",
                ))
            }
        };

        Ok(())
    }

    pub fn cfg_meta(&mut self, meta: &Meta) -> syn::Result<()> {
        self.params.cfg = Some(meta.clone());
        Ok(())
    }

    pub fn outer_attrs(&mut self, list: &Punctuated<NestedMeta, Comma>) -> syn::Result<()> {
        if self.params.outer_attrs.is_empty() {
            self.params.outer_attrs = list.clone();
        } else {
            self.params.outer_attrs.extend(list.into_iter().cloned());
        }
        Ok(())
    }

    pub fn inner_attr_str(&mut self, lit: &syn::Lit) -> syn::Result<()> {
        self.params.inner_attrs.push(NestedMeta::Lit(lit.clone()));
        Ok(())
    }

    pub fn inner_attr(&mut self, meta: &Meta) -> syn::Result<()> {
        self.params.inner_attrs.push(NestedMeta::Meta(meta.clone()));
        Ok(())
    }

    pub fn version_or_inner_attr(
        &mut self,
        name: &str,
        list: &Punctuated<NestedMeta, Comma>,
        meta: &Meta,
    ) -> syn::Result<()> {
        if let Some(kind) = ConvertMode::from_str(name) {
            self.version(kind, list)?;
        } else {
            self.params.inner_attrs.push(NestedMeta::Meta(meta.clone()));
        };
        Ok(())
    }

    pub fn inner_attrs(&mut self, list: &Punctuated<NestedMeta, Comma>) -> syn::Result<()> {
        if self.params.inner_attrs.is_empty() {
            self.params.inner_attrs = list.clone();
        } else {
            self.params.inner_attrs.extend(list.into_iter().cloned());
        }
        Ok(())
    }

    pub fn version(
        &mut self,
        kind: ConvertMode,
        list: &Punctuated<NestedMeta, Comma>,
    ) -> syn::Result<()> {
        let inner = MacroParameters::from_args(list)?;
        self.params.versions.push(MacroParameterVersion {
            kind,
            params: inner,
        });
        Ok(())
    }

    pub fn drop_attrs(&mut self, meta: &Punctuated<NestedMeta, Comma>) -> syn::Result<()> {
        for nm in meta {
            match nm {
                NestedMeta::Meta(Meta::Path(path)) => {
                    let name = path
                        .get_ident()
                        .ok_or(syn::Error::new_spanned(
                            path.to_token_stream(),
                            "Expected ident",
                        ))?
                        .to_string();
                    self.params.drop_attrs.push(name);
                }
                _ => {
                    return Err(syn::Error::new_spanned(
                        nm.to_token_stream(),
                        "Expected list of idents",
                    ))
                }
            }
        }
        Ok(())
    }

    pub fn replace_feature(&mut self, meta: &Punctuated<NestedMeta, Comma>) -> syn::Result<()> {
        match meta.len() {
            2 => {
                let prev = match &meta[0] {
                    NestedMeta::Lit(Lit::Str(lit)) => lit.value(),
                    nm @ _ => {
                        return Err(syn::Error::new_spanned(
                            nm.to_token_stream(),
                            "Expected string literal",
                        ))
                    }
                };
                let new = match &meta[1] {
                    NestedMeta::Lit(Lit::Str(lit)) => lit.value(),
                    nm @ _ => {
                        return Err(syn::Error::new_spanned(
                            nm.to_token_stream(),
                            "Expected string literal",
                        ))
                    }
                };

                self.params.replace_features.insert(prev, new);
            }
            _ => {
                return Err(syn::Error::new_spanned(
                    meta.to_token_stream(),
                    "Expected two string literals",
                ))
            }
        };

        Ok(())
    }

    pub fn build(mut self) -> syn::Result<MacroParameters> {
        let mut versions = std::mem::replace(&mut self.params.versions, vec![]);

        for version in &mut versions {
            MacroParameters::apply_parent(&mut version.params, &self.params)?;

            if version.params.key.is_none() {
                version.params.key = Some(version.kind.to_str().to_string());
            }
        }

        self.params.versions = versions;

        Ok(self.params)
    }
}
