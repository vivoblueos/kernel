// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

// The names of these types are the C names, by definition: the header and
// the implementation have to agree on them.
#![allow(non_camel_case_types)]

//! The C ABI types of the POSIX synchronization objects.
//!
//! newlib describes the POSIX synchronization objects as four-byte
//! identifiers:
//!
//! ```c
//! typedef __uint32_t pthread_mutex_t;
//! typedef __uint32_t pthread_cond_t;
//! typedef __uint32_t pthread_rwlock_t;
//! ```
//!
//! That is newlib's own implementation strategy - it keeps the objects in a
//! process-wide table and hands out indices. This kernel does not: the
//! objects live in `librs/src/sync/`, and they are the real thing (a mutex is
//! a lock word plus a recursive counter plus its type).
//!
//! The two representations cannot be mixed. A C program that declares a
//! `pthread_mutex_t` with newlib's header allocates four bytes, and the
//! kernel then writes a 24-byte mutex object into it - overwriting whatever
//! the caller had next to it on the stack. That is not a portability
//! annoyance, it is silent memory corruption, and it happens in every
//! program that uses a mutex.
//!
//! So the C ABI types are declared here, sized and aligned to match the
//! kernel's objects, and `librs/include/sys/_pthreadtypes.h` declares the
//! matching C definitions. Both sides carry assertions, so a change that
//! breaks the agreement fails the build instead of corrupting memory at run
//! time.
//!
//! The objects are opaque to the C caller: the layout below only has to be
//! large enough and aligned enough to hold the kernel's object.

use core::ffi::c_int;

/// The C library's thread identifier.
///
/// newlib's `<sys/_pthreadtypes.h>` types this as `unsigned int`, and the
/// kernel hands out 32-bit thread handles.
pub type pthread_t = u32;

/// The size of a pointer on the target, used to size the opaque objects.
const PTR_SIZE: usize = core::mem::size_of::<usize>();

/// A `pthread_mutex_t`.
///
/// The kernel's mutex is a lock word, a recursive counter, a type byte and a
/// robust flag; on a 64-bit target that is 24 bytes with an 8-byte
/// alignment.
#[repr(C, align(8))]
pub struct pthread_mutex_t {
    pub(crate) __opaque: [u8; 24],
}

/// A `pthread_cond_t`.
///
/// The kernel's condition variable is two counters plus the clock its
/// deadlines are measured on: 24 bytes, 8-byte aligned.
#[repr(C, align(8))]
pub struct pthread_cond_t {
    pub(crate) __opaque: [u8; 24],
}

/// A `pthread_rwlock_t`.
///
/// The kernel's reader/writer lock is a single state word.
#[repr(C, align(8))]
pub struct pthread_rwlock_t {
    pub(crate) __opaque: [u8; PTR_SIZE],
}

/// A `pthread_barrier_t`.
///
/// The kernel's barrier is a count, a generation counter, a mutex and a
/// condition variable.
#[repr(C, align(8))]
pub struct pthread_barrier_t {
    pub(crate) __opaque: [u8; 48],
}

/// A `pthread_spinlock_t`.
#[repr(C, align(4))]
pub struct pthread_spinlock_t {
    pub(crate) __opaque: [u8; 4],
}

/// A `pthread_mutexattr_t`.
///
/// The attribute is not opaque: the caller sets the type in it, and the
/// kernel reads it back. The type is therefore the kernel's own attribute
/// structure, so the two can never drift apart.
pub type pthread_mutexattr_t = super::mutex::MutexAttr;

/// A `pthread_condattr_t`.
///
/// The clock id and the pshared flag, in that order.
pub type pthread_condattr_t = super::cond::CondAttr;

/// A `pthread_rwlockattr_t`.
pub type pthread_rwlockattr_t = super::rwlock::RwlockAttr;

/// A `pthread_barrierattr_t`.
pub type pthread_barrierattr_t = super::barrier::BarrierAttr;

/// A `pthread_attr_t`.
///
/// The stack size plus the room the kernel keeps for the other attributes.
#[repr(C)]
pub struct pthread_attr_t {
    pub(crate) stack_size: usize,
    pub(crate) padding: [usize; 4],
}

/// A `sem_t`.
///
/// The kernel's semaphore is a single counter.
#[repr(C)]
pub struct sem_t {
    pub(crate) count: core::sync::atomic::AtomicUsize,
}

/// A `pthread_once_t`.
///
/// The C library's once-control object is two ints: whether the object has
/// been initialized, and whether the initializer has already run. The kernel
/// keeps the second one as the state word of the once protocol.
#[repr(C)]
pub struct pthread_once_t {
    pub(crate) is_initialized: core::ffi::c_int,
    pub(crate) init_executed: core::ffi::c_int,
}

/// The opaque C ABI objects have to be able to hold the kernel's objects.
///
/// The kernel writes its object into the caller's storage, so the storage
/// must be at least as large and at least as aligned. These assertions are
/// the Rust half of the agreement; the C half lives in
/// `librs/include/pthread_types.h`.
const _: () = {
    use core::mem::{align_of, size_of};

    use super::barrier::Barrier;
    use super::cond::Cond;
    use super::mutex::Mutex;
    use super::rwlock::Rwlock;

    assert!(
        size_of::<pthread_mutex_t>() >= size_of::<Mutex>()
            && align_of::<pthread_mutex_t>() >= align_of::<Mutex>(),
        "pthread_mutex_t is too small for the kernel's mutex object"
    );
    assert!(
        size_of::<pthread_cond_t>() >= size_of::<Cond>()
            && align_of::<pthread_cond_t>() >= align_of::<Cond>(),
        "pthread_cond_t is too small for the kernel's condition variable"
    );
    assert!(
        size_of::<pthread_rwlock_t>() >= size_of::<Rwlock>()
            && align_of::<pthread_rwlock_t>() >= align_of::<Rwlock>(),
        "pthread_rwlock_t is too small for the kernel's reader/writer lock"
    );
    assert!(
        size_of::<pthread_barrier_t>() >= size_of::<Barrier>()
            && align_of::<pthread_barrier_t>() >= align_of::<Barrier>(),
        "pthread_barrier_t is too small for the kernel's barrier"
    );
};
