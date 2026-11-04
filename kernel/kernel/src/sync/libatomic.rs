// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! 64 位原子操作的软件回退实现。
//!
//! 背景：thumbv8m.main（Cortex-M33/M55）与 riscv32imc 只提供到 32 位的原生
//! 原子指令，没有 64 位的 CAS。GCC 在编译 C 代码时会把 64 位原子操作降级成
//! 一组 `__atomic_*` 库调用，而 libgcc 不为这些 ABI 提供 8 字节变体，于是链接
//! 失败。内核里的 `AtomicI64`（POSIX 定时器）同样需要这条路径。
//!
//! 之前的实现是从 LLVM compiler-rt 抄来的 `atomic.c`，用 C 写成。本文件是它
//! 的 Rust 等价物：把 C 侧的 `__atomic_*` 符号原样提供出来，签名与语义不变，
//! 因此外部 C 代码与 Rust 代码都能链接到同一份实现。
//!
//! 原子性由屏蔽本地中断保证：这目标都是单核，屏蔽中断期间不存在并发
//! 访问同一地址的可能。这与内核保护自身共享状态的做法一致
//! （`crate::arch::disable_local_irq_save` / `enable_local_irq_restore`）。
//!
//! 注意：这些符号只在指针宽度不足 64 位的目标上才有意义。64 位目标
//! （aarch64、riscv64）的原生原子已经覆盖到 64 位，编译进来的旧 C 版本其实
//! 是个空翻译单元。因此本模块用 `target_pointer_width` 做了条件编译，
//! 64 位目标不导出任何符号，避免与编译器内建的 `__atomic_*` 重复定义。

#![cfg(target_pointer_width = "32")]

use core::ffi::{c_int, c_void};
use core::sync::atomic::Ordering;

/// 屏蔽本地中断执行闭包，返回其结果。
#[inline(always)]
fn with_irq_masked<R>(f: impl FnOnce() -> R) -> R {
    let saved = crate::arch::disable_local_irq_save();
    let r = f();
    crate::arch::enable_local_irq_restore(saved);
    r
}

/// 原子 8 字节读。`ptr` 必须指向至少 8 字节的有效内存。
///
/// # Safety
/// `ptr` 必须有效且可读 8 字节。
#[no_mangle]
pub unsafe extern "C" fn __atomic_load_8(ptr: *const u64, _order: c_int) -> u64 {
    with_irq_masked(|| unsafe { core::ptr::read_volatile(ptr) })
}

/// 原子 8 字节写。`ptr` 必须指向至少 8 字节的有效内存。
///
/// # Safety
/// `ptr` 必须有效且可写 8 字节。
#[no_mangle]
pub unsafe extern "C" fn __atomic_store_8(ptr: *mut u64, val: u64, _order: c_int) {
    with_irq_masked(|| unsafe { core::ptr::write_volatile(ptr, val) })
}

/// 原子 8 字节交换，返回旧值。
///
/// # Safety
/// `ptr` 必须有效且可读写 8 字节。
#[no_mangle]
pub unsafe extern "C" fn __atomic_exchange_8(ptr: *mut u64, val: u64, _order: c_int) -> u64 {
    with_irq_masked(|| unsafe {
        let old = core::ptr::read_volatile(ptr);
        core::ptr::write_volatile(ptr, val);
        old
    })
}

/// 原子 8 字节比较交换。成功时把 `desired` 写入 `*ptr` 并返回 1；失败时把
/// 当前值写入 `*expected` 并返回 0。
///
/// # Safety
/// `ptr` 必须有效且可读写 8 字节，`expected` 必须有效且可写 8 字节。
#[no_mangle]
pub unsafe extern "C" fn __atomic_compare_exchange_8(
    ptr: *mut u64,
    expected: *mut u64,
    desired: u64,
    _weak: c_int,
    _success_order: c_int,
    _failure_order: c_int,
) -> u8 {
    with_irq_masked(|| unsafe {
        let old = core::ptr::read_volatile(ptr);
        if old == core::ptr::read_volatile(expected) {
            core::ptr::write_volatile(ptr, desired);
            1
        } else {
            core::ptr::write_volatile(expected, old);
            0
        }
    })
}

/// 生成 8 字节的读-改-写原子操作，返回旧值。
macro_rules! atomic_fetch_op_8 {
    ($name:ident, $op:tt) => {
        /// 原子 8 字节读-改-写，返回旧值。
        ///
        /// # Safety
        /// `ptr` 必须有效且可读写 8 字节。
        #[no_mangle]
        pub unsafe extern "C" fn $name(ptr: *mut u64, val: u64, _order: c_int) -> u64 {
            with_irq_masked(|| unsafe {
                let old = core::ptr::read_volatile(ptr);
                core::ptr::write_volatile(ptr, old $op val);
                old
            })
        }
    };
}

atomic_fetch_op_8!(__atomic_fetch_add_8, +);
atomic_fetch_op_8!(__atomic_fetch_sub_8, -);
atomic_fetch_op_8!(__atomic_fetch_and_8, &);
atomic_fetch_op_8!(__atomic_fetch_or_8, |);
atomic_fetch_op_8!(__atomic_fetch_xor_8, ^);

// ---------------------------------------------------------------------------
// 1/2/4 字节变体 —— 只给没有 A 扩展的 riscv32 用
//
// thumbv8m 与 riscv64/aarch64 都有原生的 1/2/4 字节原子，编译器不会为它们
// 生成 `__atomic_*_1/2/4` 调用，libgcc 也不导出这些符号；但 riscv32imc 连
// 32 位原子指令都没有，rustc 会把所有 `AtomicU32`/`AtomicUsize` 降级成对这
// 组符号的调用。少了它们，riscv32 的内核镜像直接链接失败。
//
// 用 `cfg(target_arch = "riscv32")` 门控，避免在其他目标上与编译器内建或
// libgcc 的同名符号重复定义。
// ---------------------------------------------------------------------------
#[cfg(target_arch = "riscv32")]
macro_rules! atomic_variants {
    ($ty:ty, $load:ident, $store:ident, $exchange:ident, $cas:ident,
     $fadd:ident, $fsub:ident, $fand:ident, $or_:ident, $fxor:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $load(ptr: *const $ty, _order: c_int) -> $ty {
            with_irq_masked(|| unsafe { core::ptr::read_volatile(ptr) })
        }

        #[no_mangle]
        pub unsafe extern "C" fn $store(ptr: *mut $ty, val: $ty, _order: c_int) {
            with_irq_masked(|| unsafe { core::ptr::write_volatile(ptr, val) })
        }

        #[no_mangle]
        pub unsafe extern "C" fn $exchange(ptr: *mut $ty, val: $ty, _order: c_int) -> $ty {
            with_irq_masked(|| unsafe {
                let old = core::ptr::read_volatile(ptr);
                core::ptr::write_volatile(ptr, val);
                old
            })
        }

        #[no_mangle]
        pub unsafe extern "C" fn $cas(
            ptr: *mut $ty,
            expected: *mut $ty,
            desired: $ty,
            _weak: c_int,
            _success_order: c_int,
            _failure_order: c_int,
        ) -> u8 {
            with_irq_masked(|| unsafe {
                let old = core::ptr::read_volatile(ptr);
                if old == core::ptr::read_volatile(expected) {
                    core::ptr::write_volatile(ptr, desired);
                    1
                } else {
                    core::ptr::write_volatile(expected, old);
                    0
                }
            })
        }

        #[no_mangle]
        pub unsafe extern "C" fn $fadd(ptr: *mut $ty, val: $ty, _order: c_int) -> $ty {
            with_irq_masked(|| unsafe {
                let old = core::ptr::read_volatile(ptr);
                core::ptr::write_volatile(ptr, old.wrapping_add(val));
                old
            })
        }

        #[no_mangle]
        pub unsafe extern "C" fn $fsub(ptr: *mut $ty, val: $ty, _order: c_int) -> $ty {
            with_irq_masked(|| unsafe {
                let old = core::ptr::read_volatile(ptr);
                core::ptr::write_volatile(ptr, old.wrapping_sub(val));
                old
            })
        }

        #[no_mangle]
        pub unsafe extern "C" fn $fand(ptr: *mut $ty, val: $ty, _order: c_int) -> $ty {
            with_irq_masked(|| unsafe {
                let old = core::ptr::read_volatile(ptr);
                core::ptr::write_volatile(ptr, old & val);
                old
            })
        }

        #[no_mangle]
        pub unsafe extern "C" fn $or_(ptr: *mut $ty, val: $ty, _order: c_int) -> $ty {
            with_irq_masked(|| unsafe {
                let old = core::ptr::read_volatile(ptr);
                core::ptr::write_volatile(ptr, old | val);
                old
            })
        }

        #[no_mangle]
        pub unsafe extern "C" fn $fxor(ptr: *mut $ty, val: $ty, _order: c_int) -> $ty {
            with_irq_masked(|| unsafe {
                let old = core::ptr::read_volatile(ptr);
                core::ptr::write_volatile(ptr, old ^ val);
                old
            })
        }
    };
}

#[cfg(target_arch = "riscv32")]
atomic_variants!(
    u8,
    __atomic_load_1,
    __atomic_store_1,
    __atomic_exchange_1,
    __atomic_compare_exchange_1,
    __atomic_fetch_add_1,
    __atomic_fetch_sub_1,
    __atomic_fetch_and_1,
    __atomic_fetch_or_1,
    __atomic_fetch_xor_1
);

#[cfg(target_arch = "riscv32")]
atomic_variants!(
    u16,
    __atomic_load_2,
    __atomic_store_2,
    __atomic_exchange_2,
    __atomic_compare_exchange_2,
    __atomic_fetch_add_2,
    __atomic_fetch_sub_2,
    __atomic_fetch_and_2,
    __atomic_fetch_or_2,
    __atomic_fetch_xor_2
);

#[cfg(target_arch = "riscv32")]
atomic_variants!(
    u32,
    __atomic_load_4,
    __atomic_store_4,
    __atomic_exchange_4,
    __atomic_compare_exchange_4,
    __atomic_fetch_add_4,
    __atomic_fetch_sub_4,
    __atomic_fetch_and_4,
    __atomic_fetch_or_4,
    __atomic_fetch_xor_4
);

// ---------------------------------------------------------------------------
// 通用（size 在运行时才知道）的变体
//
// C 代码里 `__atomic_load` 等符号带一个 size 参数，编译器在无法静态确定
// 宽度时调用它们。签名与 compiler-rt 保持一致：size 取字节数（1/2/4/8/16）。
// ---------------------------------------------------------------------------

/// 原子读，按 `size` 字节拷贝到 `dest`。
///
/// # Safety
/// `src` 必须有效且可读 `size` 字节，`dest` 必须有效且可写 `size` 字节，
/// `size` 必须是 1、2、4、8 或 16。
#[no_mangle]
pub unsafe extern "C" fn __atomic_load(
    size: c_int,
    src: *const c_void,
    dest: *mut c_void,
    _model: c_int,
) {
    match size {
        1 => copy_bytes::<1>(src, dest),
        2 => copy_bytes::<2>(src, dest),
        4 => copy_bytes::<4>(src, dest),
        8 => copy_bytes::<8>(src, dest),
        16 => copy_bytes::<16>(src, dest),
        _ => {}
    }
}

/// 原子写，把 `src` 的 `size` 字节拷贝到 `dest`。
///
/// # Safety
/// `src` 必须有效且可读 `size` 字节，`dest` 必须有效且可写 `size` 字节，
/// `size` 必须是 1、2、4、8 或 16。
#[no_mangle]
pub unsafe extern "C" fn __atomic_store(
    size: c_int,
    dest: *mut c_void,
    src: *const c_void,
    _model: c_int,
) {
    match size {
        1 => copy_bytes::<1>(src, dest),
        2 => copy_bytes::<2>(src, dest),
        4 => copy_bytes::<4>(src, dest),
        8 => copy_bytes::<8>(src, dest),
        16 => copy_bytes::<16>(src, dest),
        _ => {}
    }
}

/// 原子交换：把 `val` 写入 `*ptr`，旧值写入 `*old`。
///
/// # Safety
/// `ptr` 必须有效且可读写 `size` 字节，`val` 与 `old` 必须有效且可读写
/// `size` 字节，`size` 必须是 1、2、4、8 或 16。
#[no_mangle]
pub unsafe extern "C" fn __atomic_exchange(
    size: c_int,
    ptr: *mut c_void,
    val: *const c_void,
    old: *mut c_void,
    _model: c_int,
) {
    match size {
        1 => exchange_bytes::<1>(ptr, val, old),
        2 => exchange_bytes::<2>(ptr, val, old),
        4 => exchange_bytes::<4>(ptr, val, old),
        8 => exchange_bytes::<8>(ptr, val, old),
        16 => exchange_bytes::<16>(ptr, val, old),
        _ => {}
    }
}

/// 原子比较交换。成功返回 1 并把 `desired` 写入 `*ptr`；失败返回 0 并把
/// `*ptr` 当前值写入 `*expected`。
///
/// # Safety
/// `ptr`、`expected`、`desired` 都必须有效且可读写 `size` 字节，`size` 必须是
/// 1、2、4、8 或 16。
#[no_mangle]
pub unsafe extern "C" fn __atomic_compare_exchange(
    size: c_int,
    ptr: *mut c_void,
    expected: *mut c_void,
    desired: *const c_void,
    _success: c_int,
    _failure: c_int,
) -> c_int {
    match size {
        1 => compare_exchange_bytes::<1>(ptr, expected, desired),
        2 => compare_exchange_bytes::<2>(ptr, expected, desired),
        4 => compare_exchange_bytes::<4>(ptr, expected, desired),
        8 => compare_exchange_bytes::<8>(ptr, expected, desired),
        16 => compare_exchange_bytes::<16>(ptr, expected, desired),
        _ => 0,
    }
}

/// 该尺寸的原子操作是否无需加锁。指针宽度 32 位时，8 字节与 16 字节都
/// 需要软件回退，其余宽度都有原生指令。
///
/// # Safety
/// `ptr` 必须有效。
#[no_mangle]
pub unsafe extern "C" fn __atomic_is_lock_free(size: usize, _ptr: *mut c_void) -> bool {
    matches!(size, 1 | 2 | 4)
}

/// 在屏蔽中断的保护下拷贝 `N` 字节。
///
/// # Safety
/// `src` 必须有效且可读 `N` 字节，`dest` 必须有效且可写 `N` 字节。
#[inline(always)]
unsafe fn copy_bytes<const N: usize>(src: *const c_void, dest: *mut c_void) {
    with_irq_masked(|| unsafe {
        core::ptr::copy_nonoverlapping(src as *const u8, dest as *mut u8, N);
    });
}

/// 在屏蔽中断的保护下交换 `N` 字节。
///
/// # Safety
/// `ptr` 必须有效且可读写 `N` 字节，`val` 与 `old` 必须有效且可读写 `N` 字节。
#[inline(always)]
unsafe fn exchange_bytes<const N: usize>(
    ptr: *mut c_void,
    val: *const c_void,
    old: *mut c_void,
) {
    with_irq_masked(|| unsafe {
        core::ptr::copy_nonoverlapping(ptr as *const u8, old as *mut u8, N);
        core::ptr::copy_nonoverlapping(val as *const u8, ptr as *mut u8, N);
    });
}

/// 在屏蔽中断的保护下比较交换 `N` 字节。
///
/// # Safety
/// `ptr`、`expected`、`desired` 都必须有效且可读写 `N` 字节。
#[inline(always)]
unsafe fn compare_exchange_bytes<const N: usize>(
    ptr: *mut c_void,
    expected: *mut c_void,
    desired: *const c_void,
) -> c_int {
    with_irq_masked(|| unsafe {
        let mut buf = [0u8; N];
        core::ptr::copy_nonoverlapping(ptr as *const u8, buf.as_mut_ptr(), N);
        if buf.as_slice() == core::slice::from_raw_parts(expected as *const u8, N) {
            core::ptr::copy_nonoverlapping(desired as *const u8, ptr as *mut u8, N);
            1
        } else {
            core::ptr::copy_nonoverlapping(buf.as_ptr(), expected as *mut u8, N);
            0
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    // The built-in `#[test]` expands to a `TestDescAndFn`, which does not match
    // the kernel's `&[&dyn Fn()]` unittest runner.
    use blueos_test_macro::test;

    // `AtomicU64` cannot be used here: this module only exists for targets
    // without native 64-bit atomics, and those are exactly the targets where
    // the type is not available. A plain `u64` is 8-byte aligned on all of
    // them, which is what the 8-byte helpers need.
    #[test]
    fn load_store_roundtrip() {
        let mut v = 0u64;
        unsafe {
            __atomic_store_8(&mut v as *mut u64, 0x1234_5678_9abc_def0, 0);
            assert_eq!(
                __atomic_load_8(&v as *const u64, 0),
                0x1234_5678_9abc_def0
            );
        }
    }

    #[test]
    fn exchange_returns_old_value() {
        let mut v = 42u64;
        let old = unsafe { __atomic_exchange_8(&mut v as *mut u64, 7, 0) };
        assert_eq!(old, 42);
        assert_eq!(v, 7);
    }

    #[test]
    fn compare_exchange_succeeds_on_match() {
        let mut v = 5u64;
        let mut expected = 5u64;
        let r = unsafe {
            __atomic_compare_exchange_8(&mut v as *mut u64, &mut expected as *mut u64, 9, 0, 0, 0)
        };
        assert_eq!(r, 1);
        assert_eq!(v, 9);
    }

    #[test]
    fn compare_exchange_fails_on_mismatch() {
        let mut v = 5u64;
        let mut expected = 3u64;
        let r = unsafe {
            __atomic_compare_exchange_8(&mut v as *mut u64, &mut expected as *mut u64, 9, 0, 0, 0)
        };
        assert_eq!(r, 0);
        assert_eq!(v, 5);
        assert_eq!(expected, 5);
    }

    #[test]
    fn fetch_ops_return_previous_value() {
        let mut v = 10u64;
        unsafe {
            assert_eq!(__atomic_fetch_add_8(&mut v as *mut u64, 5, 0), 10);
        }
        assert_eq!(v, 15);
        unsafe {
            assert_eq!(__atomic_fetch_sub_8(&mut v as *mut u64, 3, 0), 15);
        }
        assert_eq!(v, 12);
        unsafe {
            assert_eq!(__atomic_fetch_xor_8(&mut v as *mut u64, 0xff, 0), 12);
        }
        assert_eq!(v, 12 ^ 0xff);
    }

    #[test]
    fn generic_size_variants_work() {
        // The source must be a separate object: `__atomic_store` copies through
        // `copy_nonoverlapping`, and passing `&v` while also writing to `&mut v`
        // trips the overlap precondition check.
        let mut v = 0u32;
        let src = 1u32;
        let mut out = 0u32;
        unsafe {
            __atomic_store(
                4,
                &mut v as *mut u32 as *mut c_void,
                &src as *const u32 as *const c_void,
                0,
            );
            __atomic_load(
                4,
                &v as *const u32 as *const c_void,
                &mut out as *mut u32 as *mut c_void,
                0,
            );
        }
        assert_eq!(out, 1);

        let mut old = 0u32;
        let two = 2u32;
        unsafe {
            __atomic_exchange(
                4,
                &mut v as *mut u32 as *mut c_void,
                &two as *const u32 as *const c_void,
                &mut old as *mut u32 as *mut c_void,
                0,
            );
        }
        assert_eq!(old, 1);
        assert_eq!(v, 2);
    }
}
