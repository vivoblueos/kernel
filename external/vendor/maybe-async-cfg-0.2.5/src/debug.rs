#[cfg(feature="debug")]
pub mod inner {

    use proc_macro::TokenStream;
    use proc_macro2::TokenStream as TokenStream2;
    
    use crate::params::MacroParameters;
    
    ////////////////////////////////////////////////////////////////////////////////////////////////
    
    pub fn dump_maybe(args: &TokenStream, input: &TokenStream) {
        println!("--vvv------------------------------------------");
        println!("maybe:");
        println!("args:");
        println!("{}", args);
        println!("input:");
        println!("{}", input);
        println!("--^^^------------------------------------------");
        println!("");
    }

    pub fn dump_tokens(name: &str, ts: &TokenStream) {
        println!("--vvv------------------------------------------");
        println!("{}:", name);
        println!("{}", ts);
        println!("--^^^------------------------------------------");
        println!("");
    }

    pub fn dump_tokens2(name: &str, ts: &TokenStream2) {
        println!("--vvv------------------------------------------");
        println!("{}:", name);
        println!("{}", ts);
        println!("--^^^------------------------------------------");
        println!("");
    }
    
    pub fn dump_params(name: &str, params: &MacroParameters) {
        println!("--vvv------------------------------------------");
        println!("{}:", name);
        println!("{:#?}", params);
        println!("--^^^------------------------------------------");
        println!("");
    }

}

////////////////////////////////////////////////////////////////////////////////////////////////////

macro_rules! dump_maybe {
    ($args:expr, $input:expr) => {
        #[cfg(feature="debug")]
        crate::debug::inner::dump_maybe($args, $input);
    }
}
pub(crate) use dump_maybe;

macro_rules! dump_tokens {
    ($name:expr, $ts:expr) => {
        #[cfg(feature="debug")]
        crate::debug::inner::dump_tokens($name, $ts);
    }
}
pub(crate) use dump_tokens;

macro_rules! dump_tokens2 {
    ($name:expr, $ts:expr) => {
        #[cfg(feature="debug")]
        crate::debug::inner::dump_tokens2($name, $ts);
    }
}
pub(crate) use dump_tokens2;

macro_rules! dump_params {
    ($name:expr, $params:expr) => {
        #[cfg(feature="debug")]
        crate::debug::inner::dump_params($name, $params);
    }
}
pub(crate) use dump_params;
