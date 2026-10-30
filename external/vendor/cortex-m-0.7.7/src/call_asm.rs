/// An internal macro to invoke an assembly routine.
///
/// Depending on whether the unstable `inline-asm` feature is enabled, this will either call into
/// the inline assembly implementation directly, or through the FFI shim (see `asm/lib.rs`).
macro_rules! call_asm {
    ( $func:ident ( $($args:ident: $tys:ty),* ) $(-> $ret:ty)? ) => {{
        #[allow(unused_unsafe)]
        unsafe {
            match () {
                #[cfg(feature = "inline-asm")]
                () => crate::asm::inline::$func($($args),*),

                #[cfg(not(feature = "inline-asm"))]
                () => {
                    extern "C" {
                        fn $func($($args: $tys),*) $(-> $ret)?;
                    }

                    $func($($args),*)
                },
            }
        }
    }};
}
