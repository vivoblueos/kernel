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

// Newlib retargetable locking adapters.
//
// When newlib is built with --enable-newlib-retargetable-locking (_RETARGETABLE_LOCKING),
// it requires the target to provide:
//   1. struct __lock — opaque lock type
//   2. 8 static globals: struct __lock __lock___*_{mutex,recursive_mutex}
//   3. __retarget_lock_* functions operating on _LOCK_T = struct __lock *
//
// _LOCK_RECURSIVE_T = _LOCK_T (same pointer type), so struct __lock must hold
// both normal and recursive locks. We use a #[repr(C)] tagged union approach:
//   - Normal locks contain GenericMutex<()> (futex-based, non-recursive)
//   - Recursive locks contain Mutex with Ty::Recursive (reentrant, tracks count)

use crate::syncs::{new_recursive_mutex, GenericMutex, Mutex};
use alloc::boxed::Box;
use core::{ffi::c_int, mem::ManuallyDrop};

#[repr(C)]
#[derive(Clone, Copy)]
enum LockKind {
    Normal,
    Recursive,
}

// The opaque lock type newlib expects: struct __lock.
// A tagged union large enough for GenericMutex<()> or Mutex.
#[repr(C)]
pub struct __lock {
    kind: LockKind,
    storage: LockStorage,
}

#[repr(C)]
union LockStorage {
    normal: ManuallyDrop<GenericMutex<()>>,
    recursive: ManuallyDrop<Mutex>,
}

impl __lock {
    const fn new_normal() -> Self {
        Self {
            kind: LockKind::Normal,
            storage: LockStorage {
                normal: ManuallyDrop::new(GenericMutex::new(())),
            },
        }
    }

    const fn new_recursive() -> Self {
        Self {
            kind: LockKind::Recursive,
            storage: LockStorage {
                recursive: ManuallyDrop::new(new_recursive_mutex()),
            },
        }
    }

    fn acquire(&self) {
        match self.kind {
            LockKind::Normal => unsafe {
                (*self.storage.normal).manual_lock();
            },
            LockKind::Recursive => unsafe {
                (*self.storage.recursive).lock().ok();
            },
        }
    }

    fn try_acquire(&self) -> c_int {
        match self.kind {
            LockKind::Normal => unsafe {
                match (*self.storage.normal).manual_try_lock() {
                    Ok(_) => 0,
                    Err(_) => 1,
                }
            },
            LockKind::Recursive => unsafe {
                match (*self.storage.recursive).try_lock() {
                    Ok(_) => 0,
                    Err(_) => 1,
                }
            },
        }
    }

    fn release(&self) {
        match self.kind {
            LockKind::Normal => unsafe {
                (*self.storage.normal).manual_unlock();
            },
            LockKind::Recursive => unsafe {
                (*self.storage.recursive).unlock().ok();
            },
        }
    }
}

// Static lock globals matching newlib's BSS symbols.
// Recursive-named locks use recursive mutex type; others use normal.

#[no_mangle]
static __lock___sfp_recursive_mutex: __lock = __lock::new_recursive();

#[no_mangle]
static __lock___atexit_recursive_mutex: __lock = __lock::new_recursive();

#[no_mangle]
static __lock___at_quick_exit_mutex: __lock = __lock::new_normal();

#[no_mangle]
static __lock___malloc_recursive_mutex: __lock = __lock::new_recursive();

#[no_mangle]
static __lock___env_recursive_mutex: __lock = __lock::new_recursive();

#[no_mangle]
static __lock___tz_mutex: __lock = __lock::new_normal();

#[no_mangle]
static __lock___dd_hash_mutex: __lock = __lock::new_normal();

#[no_mangle]
static __lock___arc4random_mutex: __lock = __lock::new_normal();

// __retarget_lock_* implementations.
// _LOCK_T = *mut __lock. Init functions take *mut *mut __lock and may
// replace the pointer with a heap-allocated lock.

#[no_mangle]
pub unsafe extern "C" fn __retarget_lock_init(lock: *mut *mut __lock) {
    *lock = Box::into_raw(Box::new(__lock::new_normal()));
}

#[no_mangle]
pub unsafe extern "C" fn __retarget_lock_init_recursive(lock: *mut *mut __lock) {
    *lock = Box::into_raw(Box::new(__lock::new_recursive()));
}

#[no_mangle]
pub unsafe extern "C" fn __retarget_lock_close(lock: *mut __lock) {
    if !lock.is_null() {
        drop(Box::from_raw(lock));
    }
}

#[no_mangle]
pub unsafe extern "C" fn __retarget_lock_close_recursive(lock: *mut __lock) {
    __retarget_lock_close(lock);
}

#[no_mangle]
pub unsafe extern "C" fn __retarget_lock_acquire(lock: *mut __lock) {
    if !lock.is_null() {
        (*lock).acquire();
    }
}

#[no_mangle]
pub unsafe extern "C" fn __retarget_lock_acquire_recursive(lock: *mut __lock) {
    __retarget_lock_acquire(lock);
}

#[no_mangle]
pub unsafe extern "C" fn __retarget_lock_try_acquire(lock: *mut __lock) -> c_int {
    if lock.is_null() {
        return 0;
    }
    (*lock).try_acquire()
}

#[no_mangle]
pub unsafe extern "C" fn __retarget_lock_try_acquire_recursive(lock: *mut __lock) -> c_int {
    __retarget_lock_try_acquire(lock)
}

#[no_mangle]
pub unsafe extern "C" fn __retarget_lock_release(lock: *mut __lock) {
    if !lock.is_null() {
        (*lock).release();
    }
}

#[no_mangle]
pub unsafe extern "C" fn __retarget_lock_release_recursive(lock: *mut __lock) {
    __retarget_lock_release(lock);
}
