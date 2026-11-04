# Invoke a syscall

BlueOS kernel offers two modes of invoking syscall.

1. Software interruption

This is generally seen in most OS kernels to switch from user space to kernel space.

2. Direct invoking

In this mode, syscall handlers are invoked directly via function calls.

In both modes, if you have to invoke a syscall, use the `bk_syscall!` macro in `blueos_scal` crate.
For example,
```
use blueos_scal::bk_syscall;
use blueos_header::syscalls::NR::{Read};

fn read_something(fd: i32, buf: *mut i8, len: usize) -> i32 {
    bk_syscall!(Read, buf, len) as i32
}
```
There is no need to change your code when switching to another mode.
By default, SWI mode is used. If you want to use the direct invoking mode,
what you have to do is passing `--cfg direct_syscall_handler` to build the kernel.
