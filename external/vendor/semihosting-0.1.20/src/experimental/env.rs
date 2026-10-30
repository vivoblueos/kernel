// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(clippy::undocumented_unsafe_blocks)] // TODO

use core::{fmt, str};

use crate::io;

/// An iterator over the arguments of a process, yielding a `Result<&str>` value for
/// each argument.
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Args<const BUF_SIZE: usize>(sys::ArgsBytes<BUF_SIZE>);

/// Returns the arguments that this program was started with.
pub fn args<const BUF_SIZE: usize>() -> io::Result<Args<BUF_SIZE>> {
    sys::args_bytes().map(Args)
}

#[allow(clippy::copy_iterator)] // TODO
impl<'a, const BUF_SIZE: usize> Iterator for &'a Args<BUF_SIZE> {
    type Item = Result<&'a str, str::Utf8Error>;
    fn next(&mut self) -> Option<Self::Item> {
        let arg = (&self.0).next()?;
        Some(str::from_utf8(arg))
    }
}

impl<const BUF_SIZE: usize> fmt::Debug for Args<BUF_SIZE> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Args").finish_non_exhaustive()
    }
}

mod sys {
    pub(crate) use self::imp::{ArgsBytes, args_bytes};

    const NUL: u8 = b'\0';

    fn next_from_cmdline<'a, const BUF_SIZE: usize>(
        args: &mut &'a ArgsBytes<BUF_SIZE>,
    ) -> Option<&'a [u8]> {
        if args.next.get() >= args.size {
            return None;
        }
        let mut start = args.next.get();
        let mut end = None;
        let is_blank = |b: u8| b == b' ' || b == b'\t';
        let mut delim = NUL;
        let mut in_argument = false;
        while args.next.get() < args.size {
            let b = args.buf[args.next.get()];
            if !in_argument {
                if is_blank(b) {
                    end = Some(args.next.get());
                    args.next.set(args.next.get() + 1);
                    break;
                }
                if b == b'"' || b == b'\'' {
                    delim = b;
                    start += 1;
                }
                in_argument = true;
            } else if delim != NUL {
                if b == delim {
                    end = Some(args.next.get());
                    args.next.set(args.next.get() + 2);
                    break;
                }
            } else if is_blank(b) {
                end = Some(args.next.get());
                args.next.set(args.next.get() + 1);
                break;
            }

            args.next.set(args.next.get() + 1);
        }
        Some(&args.buf[start..end.unwrap_or_else(|| args.next.get())])
    }

    #[cfg(any(
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "riscv32",
        target_arch = "riscv64",
        all(target_arch = "xtensa", feature = "openocd-semihosting"),
    ))]
    mod imp {
        use core::cell::Cell;

        use super::{NUL, next_from_cmdline};
        use crate::{
            io,
            sys::arm_compat::{CommandLine, sys_get_cmdline},
        };

        pub(crate) struct ArgsBytes<const BUF_SIZE: usize> {
            pub(super) buf: [u8; BUF_SIZE],
            pub(super) next: Cell<usize>,
            pub(super) size: usize,
        }
        pub(crate) fn args_bytes<const BUF_SIZE: usize>() -> io::Result<ArgsBytes<BUF_SIZE>> {
            let mut buf = [0; BUF_SIZE];
            let mut cmdline_block = CommandLine { ptr: buf.as_mut_ptr(), size: BUF_SIZE - 1 };
            unsafe {
                sys_get_cmdline(&mut cmdline_block)?;
            }
            debug_assert!(!cmdline_block.ptr.is_null());
            if cmdline_block.size > BUF_SIZE - 1 || buf[BUF_SIZE - 1] != NUL {
                return Err(io::ErrorKind::ArgumentListTooLong.into());
            }
            Ok(ArgsBytes { buf, next: Cell::new(0), size: cmdline_block.size })
        }
        #[allow(clippy::copy_iterator)] // TODO
        impl<'a, const BUF_SIZE: usize> Iterator for &'a ArgsBytes<BUF_SIZE> {
            type Item = &'a [u8];
            fn next(&mut self) -> Option<Self::Item> {
                next_from_cmdline(self)
            }
        }
    }
    #[cfg(any(
        target_arch = "mips",
        target_arch = "mips32r6",
        target_arch = "mips64",
        target_arch = "mips64r6",
    ))]
    mod imp {

        use core::cell::Cell;

        use super::{NUL, next_from_cmdline};
        use crate::{
            io,
            sys::mips::{mips_argc, mips_argn, mips_argnlen},
        };

        pub(crate) struct ArgsBytes<const BUF_SIZE: usize> {
            pub(super) buf: [u8; BUF_SIZE],
            pub(super) next: Cell<usize>,
            pub(super) size: usize,
            next_fn: for<'a> fn(&mut &'a ArgsBytes<BUF_SIZE>) -> Option<&'a [u8]>,
        }
        pub(crate) fn args_bytes<const BUF_SIZE: usize>() -> io::Result<ArgsBytes<BUF_SIZE>> {
            let mut buf = [0; BUF_SIZE];
            let argc = mips_argc();
            let mut start = 0;
            for i in 0..argc {
                let len = mips_argnlen(i)? + 1;
                if start + len > BUF_SIZE {
                    return Err(io::ErrorKind::ArgumentListTooLong.into());
                }
                unsafe {
                    mips_argn(i, buf.as_mut_ptr().add(start))?;
                    start += len;
                }
            }
            Ok(ArgsBytes {
                buf,
                next: Cell::new(0),
                size: start,
                next_fn: if argc == 1 { next_from_cmdline } else { next_from_args },
            })
        }
        fn next_from_args<'a, const BUF_SIZE: usize>(
            args: &mut &'a ArgsBytes<BUF_SIZE>,
        ) -> Option<&'a [u8]> {
            if args.next.get() >= args.size {
                return None;
            }
            let start = args.next.get();
            let mut end = None;
            while args.next.get() < args.size {
                let b = args.buf[args.next.get()];
                if b == NUL {
                    end = Some(args.next.get());
                    args.next.set(args.next.get() + 1);
                    break;
                }
                args.next.set(args.next.get() + 1);
            }
            let end = end.unwrap_or_else(|| args.next.get());
            let last = end.saturating_sub(1);
            if start != last
                && (args.buf[start] == b'"' && args.buf[last] == b'"'
                    || args.buf[start] == b'\'' && args.buf[last] == b'\'')
            {
                Some(&args.buf[start + 1..last])
            } else {
                Some(&args.buf[start..end])
            }
        }

        #[allow(clippy::copy_iterator)] // TODO
        impl<'a, const BUF_SIZE: usize> Iterator for &'a ArgsBytes<BUF_SIZE> {
            type Item = &'a [u8];
            fn next(&mut self) -> Option<Self::Item> {
                (self.next_fn)(self)
            }
        }
    }
}
