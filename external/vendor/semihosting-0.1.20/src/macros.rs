// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(missing_docs)] // TODO

#[cfg(feature = "stdio")]
#[cfg_attr(docsrs, doc(cfg(feature = "stdio")))]
#[macro_export]
macro_rules! print {
    ($($tt:tt)*) => {
        if let $crate::__private::Ok(mut stdout) = $crate::io::stdout() {
            use $crate::io::Write as _;
            let _ = $crate::__private::write!(stdout, $($tt)*);
        }
    };
}
#[cfg(feature = "stdio")]
#[cfg_attr(docsrs, doc(cfg(feature = "stdio")))]
#[macro_export]
macro_rules! println {
    ($($tt:tt)*) => {
        if let $crate::__private::Ok(mut stdout) = $crate::io::stdout() {
            use $crate::io::Write as _;
            let _ = $crate::__private::writeln!(stdout, $($tt)*);
        }
    };
}

#[cfg(feature = "stdio")]
#[cfg_attr(docsrs, doc(cfg(feature = "stdio")))]
#[macro_export]
macro_rules! eprint {
    ($($tt:tt)*) => {
        if let $crate::__private::Ok(mut stderr) = $crate::io::stderr() {
            use $crate::io::Write as _;
            let _ = $crate::__private::write!(stderr, $($tt)*);
        }
    };
}
#[cfg(feature = "stdio")]
#[cfg_attr(docsrs, doc(cfg(feature = "stdio")))]
#[macro_export]
macro_rules! eprintln {
    ($($tt:tt)*) => {
        if let $crate::__private::Ok(mut stderr) = $crate::io::stderr() {
            use $crate::io::Write as _;
            let _ = $crate::__private::writeln!(stderr, $($tt)*);
        }
    };
}

#[cfg(feature = "stdio")]
#[cfg_attr(docsrs, doc(cfg(feature = "stdio")))]
#[macro_export]
macro_rules! dbg {
    () => {
        $crate::eprintln!("[{}:{}]", $crate::__private::file!(), $crate::__private::line!())
    };
    ($val:expr $(,)?) => {
        match $val {
            tmp => {
                $crate::eprintln!(
                    "[{}:{}] {} = {:#?}",
                    $crate::__private::file!(),
                    $crate::__private::line!(),
                    $crate::__private::stringify!($val),
                    &tmp,
                );
                tmp
            }
        }
    };
    ($($val:expr),+ $(,)?) => {
        ($($crate::dbg!($val)),+,)
    };
}

macro_rules! static_assert {
    ($($tt:tt)*) => {
        const _: () = assert!($($tt)*);
    };
}
