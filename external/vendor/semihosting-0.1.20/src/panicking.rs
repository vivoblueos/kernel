// SPDX-License-Identifier: Apache-2.0 OR MIT

#[allow(clippy::used_underscore_binding)]
#[inline(never)]
#[cfg_attr(not(test), panic_handler)]
fn _panic(_info: &core::panic::PanicInfo<'_>) -> ! {
    #[cfg(feature = "stdio")]
    eprintln!("{_info}");

    #[cfg(feature = "panic-unwind")]
    {
        use crate::atomic::Ordering;
        // TODO: PANICKED is global, so if panics occur concurrently on thread 1 and thread 2 this
        // could be mistakenly thought to be a double panic. However, I'm not sure if there is a way
        // to handle that well without thread local.
        if crate::experimental::panic::PANICKED.fetch_add(1, Ordering::AcqRel) != 0 {
            #[cfg(feature = "stdio")]
            eprintln!("panic during panic, aborting");
            crate::process::abort()
        }
    }

    #[cfg(feature = "backtrace")]
    {
        use core::{ffi::c_void, ptr};

        use unwinding::abi::{_Unwind_Backtrace, _Unwind_GetIP, UnwindContext, UnwindReasonCode};

        extern "C" fn callback(
            unwind_ctx: &UnwindContext<'_>,
            _arg: *mut c_void,
        ) -> UnwindReasonCode {
            let ip = _Unwind_GetIP(unwind_ctx);
            if ip == 0 {
                UnwindReasonCode::NORMAL_STOP
            } else {
                eprintln!("  {ip:#x}");
                UnwindReasonCode::NO_REASON
            }
        }

        eprintln!("stack backtrace:");
        _Unwind_Backtrace(callback, ptr::null_mut());
    }

    #[cfg(feature = "panic-unwind")]
    {
        let _code = unwinding::panic::begin_panic(alloc::boxed::Box::new(""));
        #[cfg(feature = "stdio")]
        eprintln!("failed to begin panic (unwind error code {})", _code.0);
    }

    crate::process::exit(101)
}
