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

//===-- atomic.c - Implement support functions for atomic operations.------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  atomic.c defines a set of functions for performing atomic accesses on
//  arbitrary-sized memory locations.  This design uses locks that should
//  be fast in the uncontended case, for two reasons:
//
//  1) This code must work with C programs that do not link to anything
//     (including pthreads) and so it should not depend on any pthread
//     functions. If the user wishes to opt into using pthreads, they may do so.
//  2) Atomic operations, rather than explicit mutexes, are most commonly used
//     on code where contended operations are rate.
//
//  To avoid needing a per-object lock, this code allocates an array of
//  locks and hashes the object pointers to find the one that it should use.
//  For operations that must be atomic on two locations, the lower lock is
//  always acquired first, to avoid deadlock.
//
//===----------------------------------------------------------------------===//

#if __POINTER_WIDTH__ == 32

typedef unsigned long uintptr_t;
typedef long intptr_t;
typedef unsigned char bool;
typedef unsigned long size_t;
typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned long uint32_t;
typedef unsigned long long uint64_t;

// BlueKernel provides these implementations.
extern size_t disable_local_irq_save();
extern void enable_local_irq_restore(size_t);

#define true 1
#define false 0

// If RISCV's A extension is not featured, we are unable to use CAS locks.
// Atomic is guaranteed by disabling IRQs.
#if (!defined(__riscv) || defined(__riscv_atomic))
#define HAS_LOCK_FREE_CAS
#endif

#include "assembly.h"

// We use __builtin_mem* here to avoid dependencies on libc-provided headers.
#define memcpy __builtin_memcpy
#define memcmp __builtin_memcmp

// Clang objects if you redefine a builtin.  This little hack allows us to
// define a function with the same name as an intrinsic.
#pragma redefine_extname __atomic_load_c SYMBOL_NAME(__atomic_load)
#pragma redefine_extname __atomic_store_c SYMBOL_NAME(__atomic_store)
#pragma redefine_extname __atomic_exchange_c SYMBOL_NAME(__atomic_exchange)
#pragma redefine_extname __atomic_compare_exchange_c SYMBOL_NAME(              \
    __atomic_compare_exchange)
#pragma redefine_extname __atomic_is_lock_free_c SYMBOL_NAME(                  \
    __atomic_is_lock_free)

#ifdef HAS_LOCK_FREE_CAS
/// Number of locks.  This allocates one page on 32-bit platforms, two on
/// 64-bit.  This can be specified externally if a different trade between
/// memory usage and contention probability is required for a given platform.
#ifndef SPINLOCK_COUNT
#define SPINLOCK_COUNT (1 << 10)
#endif
static const long SPINLOCK_MASK = SPINLOCK_COUNT - 1;

////////////////////////////////////////////////////////////////////////////////
// Platform-specific lock implementation.  Falls back to spinlocks if none is
// defined.  Each platform should define the Lock type, and corresponding
// lock() and unlock() functions.
////////////////////////////////////////////////////////////////////////////////
_Static_assert(__atomic_always_lock_free(sizeof(uintptr_t), 0),
               "Implementation assumes lock-free pointer-size cmpxchg");
typedef _Atomic(uintptr_t) Lock;
/// Unlock a lock.  This is a release operation.
__inline static void unlock(Lock *l, size_t irq_status) {
  __c11_atomic_store(l, 0, __ATOMIC_RELEASE);
  enable_local_irq_restore(irq_status);
}
/// Locks a lock.  In the current implementation, this is potentially
/// unbounded in the contended case.
__inline static size_t lock(Lock *l) {
  size_t irq_status = disable_local_irq_save();
  uintptr_t old = 0;
  while (!__c11_atomic_compare_exchange_weak(l, &old, 1, __ATOMIC_ACQUIRE,
                                             __ATOMIC_RELAXED))
    old = 0;
  return irq_status;
}
/// locks for atomic operations
static Lock locks[SPINLOCK_COUNT];

/// Returns a lock to use for a given pointer.
static __inline Lock *lock_for_pointer(void *ptr) {
  intptr_t hash = (intptr_t)ptr;
  // Disregard the lowest 4 bits.  We want all values that may be part of the
  // same memory operation to hash to the same value and therefore use the same
  // lock.
  hash >>= 4;
  // Use the next bits as the basis for the hash
  intptr_t low = hash & SPINLOCK_MASK;
  // Now use the high(er) set of bits to perturb the hash, so that we don't
  // get collisions from atomic fields in a single object
  hash >>= 16;
  hash ^= low;
  // Return a pointer to the word to use
  return locks + (hash & SPINLOCK_MASK);
}

#else

typedef int Lock;

static __inline Lock *lock_for_pointer(void *ptr) { return 0; }

__inline static void unlock(Lock *l, size_t irq_status) {
  enable_local_irq_restore(irq_status);
}

__inline static size_t lock(Lock *l) {
  size_t irq_status = disable_local_irq_save();
  return irq_status;
}

#endif // HAS_LOCK_FREE_CAS

/// Macros for determining whether a size is lock free.
#define ATOMIC_ALWAYS_LOCK_FREE_OR_ALIGNED_LOCK_FREE(size, p)                  \
  (__atomic_always_lock_free(size, p) ||                                       \
   (__atomic_always_lock_free(size, 0) && ((uintptr_t)p % size) == 0))
#define IS_LOCK_FREE_1(p) ATOMIC_ALWAYS_LOCK_FREE_OR_ALIGNED_LOCK_FREE(1, p)
#define IS_LOCK_FREE_2(p) ATOMIC_ALWAYS_LOCK_FREE_OR_ALIGNED_LOCK_FREE(2, p)
#define IS_LOCK_FREE_4(p) ATOMIC_ALWAYS_LOCK_FREE_OR_ALIGNED_LOCK_FREE(4, p)
#define IS_LOCK_FREE_8(p) ATOMIC_ALWAYS_LOCK_FREE_OR_ALIGNED_LOCK_FREE(8, p)
#define IS_LOCK_FREE_16(p) ATOMIC_ALWAYS_LOCK_FREE_OR_ALIGNED_LOCK_FREE(16, p)

/// Macro that calls the compiler-generated lock-free versions of functions
/// when they exist.
#define TRY_LOCK_FREE_CASE(n, type, ptr)                                       \
  case n:                                                                      \
    if (IS_LOCK_FREE_##n(ptr)) {                                               \
      LOCK_FREE_ACTION(type);                                                  \
    }                                                                          \
    break;
#ifdef __SIZEOF_INT128__
#define TRY_LOCK_FREE_CASE_16(p) TRY_LOCK_FREE_CASE(16, __uint128_t, p)
#else
#define TRY_LOCK_FREE_CASE_16(p) /* __uint128_t not available */
#endif

#define LOCK_FREE_CASES(ptr)                                                   \
  do {                                                                         \
    switch (size) {                                                            \
      TRY_LOCK_FREE_CASE(1, uint8_t, ptr)                                      \
      TRY_LOCK_FREE_CASE(2, uint16_t, ptr)                                     \
      TRY_LOCK_FREE_CASE(4, uint32_t, ptr)                                     \
      TRY_LOCK_FREE_CASE(8, uint64_t, ptr)                                     \
      TRY_LOCK_FREE_CASE_16(ptr) /* __uint128_t may not be supported */        \
    default:                                                                   \
      break;                                                                   \
    }                                                                          \
  } while (0)

/// Whether atomic operations for the given size (and alignment) are lock-free.
bool __atomic_is_lock_free_c(size_t size, void *ptr) {
#define LOCK_FREE_ACTION(type) return true;
  LOCK_FREE_CASES(ptr);
#undef LOCK_FREE_ACTION
  return false;
}

/// An atomic load operation.  This is atomic with respect to the source
/// pointer only.
void __atomic_load_c(int size, void *src, void *dest, int model) {
#define LOCK_FREE_ACTION(type)                                                 \
  *((type *)dest) = __c11_atomic_load((_Atomic(type) *)src, model);            \
  return;
  LOCK_FREE_CASES(src);
#undef LOCK_FREE_ACTION
  Lock *l = lock_for_pointer(src);
  size_t irq = lock(l);
  memcpy(dest, src, size);
  unlock(l, irq);
}

/// An atomic store operation.  This is atomic with respect to the destination
/// pointer only.
void __atomic_store_c(int size, void *dest, void *src, int model) {
#define LOCK_FREE_ACTION(type)                                                 \
  __c11_atomic_store((_Atomic(type) *)dest, *(type *)src, model);              \
  return;
  LOCK_FREE_CASES(dest);
#undef LOCK_FREE_ACTION
  Lock *l = lock_for_pointer(dest);
  size_t irq = lock(l);
  memcpy(dest, src, size);
  unlock(l, irq);
}

/// Atomic compare and exchange operation.  If the value at *ptr is identical
/// to the value at *expected, then this copies value at *desired to *ptr.  If
/// they  are not, then this stores the current value from *ptr in *expected.
///
/// This function returns 1 if the exchange takes place or 0 if it fails.
int __atomic_compare_exchange_c(int size, void *ptr, void *expected,
                                void *desired, int success, int failure) {
#define LOCK_FREE_ACTION(type)                                                 \
  return __c11_atomic_compare_exchange_strong(                                 \
      (_Atomic(type) *)ptr, (type *)expected, *(type *)desired, success,       \
      failure)
  LOCK_FREE_CASES(ptr);
#undef LOCK_FREE_ACTION
  Lock *l = lock_for_pointer(ptr);
  size_t irq = lock(l);
  if (memcmp(ptr, expected, size) == 0) {
    memcpy(ptr, desired, size);
    unlock(l, irq);
    return 1;
  }
  memcpy(expected, ptr, size);
  unlock(l, irq);
  return 0;
}

/// Performs an atomic exchange operation between two pointers.  This is atomic
/// with respect to the target address.
void __atomic_exchange_c(int size, void *ptr, void *val, void *old, int model) {
#define LOCK_FREE_ACTION(type)                                                 \
  *(type *)old =                                                               \
      __c11_atomic_exchange((_Atomic(type) *)ptr, *(type *)val, model);        \
  return;
  LOCK_FREE_CASES(ptr);
#undef LOCK_FREE_ACTION
  Lock *l = lock_for_pointer(ptr);
  size_t irq = lock(l);
  memcpy(old, ptr, size);
  memcpy(ptr, val, size);
  unlock(l, irq);
}

////////////////////////////////////////////////////////////////////////////////
// Where the size is known at compile time, the compiler may emit calls to
// specialised versions of the above functions.
////////////////////////////////////////////////////////////////////////////////
#ifdef __SIZEOF_INT128__
#define OPTIMISED_CASES                                                        \
  OPTIMISED_CASE(1, IS_LOCK_FREE_1, uint8_t)                                   \
  OPTIMISED_CASE(2, IS_LOCK_FREE_2, uint16_t)                                  \
  OPTIMISED_CASE(4, IS_LOCK_FREE_4, uint32_t)                                  \
  OPTIMISED_CASE(8, IS_LOCK_FREE_8, uint64_t)                                  \
  OPTIMISED_CASE(16, IS_LOCK_FREE_16, __uint128_t)
#else
#define OPTIMISED_CASES                                                        \
  OPTIMISED_CASE(1, IS_LOCK_FREE_1, uint8_t)                                   \
  OPTIMISED_CASE(2, IS_LOCK_FREE_2, uint16_t)                                  \
  OPTIMISED_CASE(4, IS_LOCK_FREE_4, uint32_t)                                  \
  OPTIMISED_CASE(8, IS_LOCK_FREE_8, uint64_t)
#endif

#define OPTIMISED_CASE(n, lockfree, type)                                      \
  type __atomic_load_##n(type *src, int model) {                               \
    if (lockfree(src))                                                         \
      return __c11_atomic_load((_Atomic(type) *)src, model);                   \
    Lock *l = lock_for_pointer(src);                                           \
    size_t irq = lock(l);                                                      \
    type val = *src;                                                           \
    unlock(l, irq);                                                            \
    return val;                                                                \
  }
OPTIMISED_CASES
#undef OPTIMISED_CASE

#define OPTIMISED_CASE(n, lockfree, type)                                      \
  void __atomic_store_##n(type *dest, type val, int model) {                   \
    if (lockfree(dest)) {                                                      \
      __c11_atomic_store((_Atomic(type) *)dest, val, model);                   \
      return;                                                                  \
    }                                                                          \
    Lock *l = lock_for_pointer(dest);                                          \
    size_t irq = lock(l);                                                      \
    *dest = val;                                                               \
    unlock(l, irq);                                                            \
    return;                                                                    \
  }
OPTIMISED_CASES
#undef OPTIMISED_CASE

#define OPTIMISED_CASE(n, lockfree, type)                                      \
  type __atomic_exchange_##n(type *dest, type val, int model) {                \
    if (lockfree(dest))                                                        \
      return __c11_atomic_exchange((_Atomic(type) *)dest, val, model);         \
    Lock *l = lock_for_pointer(dest);                                          \
    size_t irq = lock(l);                                                      \
    type tmp = *dest;                                                          \
    *dest = val;                                                               \
    unlock(l, irq);                                                            \
    return tmp;                                                                \
  }
OPTIMISED_CASES
#undef OPTIMISED_CASE

#define OPTIMISED_CASE(n, lockfree, type)                                      \
  bool __atomic_compare_exchange_##n(type *ptr, type *expected, type desired,  \
                                     int success, int failure) {               \
    if (lockfree(ptr))                                                         \
      return __c11_atomic_compare_exchange_strong(                             \
          (_Atomic(type) *)ptr, expected, desired, success, failure);          \
    Lock *l = lock_for_pointer(ptr);                                           \
    size_t irq = lock(l);                                                      \
    if (*ptr == *expected) {                                                   \
      *ptr = desired;                                                          \
      unlock(l, irq);                                                          \
      return true;                                                             \
    }                                                                          \
    *expected = *ptr;                                                          \
    unlock(l, irq);                                                            \
    return false;                                                              \
  }
OPTIMISED_CASES
#undef OPTIMISED_CASE

////////////////////////////////////////////////////////////////////////////////
// Atomic read-modify-write operations for integers of various sizes.
////////////////////////////////////////////////////////////////////////////////
#define ATOMIC_RMW(n, lockfree, type, opname, op)                              \
  type __atomic_fetch_##opname##_##n(type *ptr, type val, int model) {         \
    if (lockfree(ptr))                                                         \
      return __c11_atomic_fetch_##opname((_Atomic(type) *)ptr, val, model);    \
    Lock *l = lock_for_pointer(ptr);                                           \
    size_t irq = lock(l);                                                      \
    type tmp = *ptr;                                                           \
    *ptr = tmp op val;                                                         \
    unlock(l, irq);                                                            \
    return tmp;                                                                \
  }

#define ATOMIC_RMW_NAND(n, lockfree, type)                                     \
  type __atomic_fetch_nand_##n(type *ptr, type val, int model) {               \
    if (lockfree(ptr))                                                         \
      return __c11_atomic_fetch_nand((_Atomic(type) *)ptr, val, model);        \
    Lock *l = lock_for_pointer(ptr);                                           \
    size_t irq = lock(l);                                                      \
    type tmp = *ptr;                                                           \
    *ptr = ~(tmp & val);                                                       \
    unlock(l, irq);                                                            \
    return tmp;                                                                \
  }

#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_RMW(n, lockfree, type, add, +)
OPTIMISED_CASES
#undef OPTIMISED_CASE
#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_RMW(n, lockfree, type, sub, -)
OPTIMISED_CASES
#undef OPTIMISED_CASE
#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_RMW(n, lockfree, type, and, &)
OPTIMISED_CASES
#undef OPTIMISED_CASE
#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_RMW(n, lockfree, type, or, |)
OPTIMISED_CASES
#undef OPTIMISED_CASE
#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_RMW(n, lockfree, type, xor, ^)
OPTIMISED_CASES
#undef OPTIMISED_CASE
// Allow build with clang without __c11_atomic_fetch_nand builtin (pre-14)
#if __has_builtin(__c11_atomic_fetch_nand)
#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_RMW_NAND(n, lockfree, type)
OPTIMISED_CASES
#undef OPTIMISED_CASE
#endif

#else  // __POINTER_WIDTH__ > 32
// We don't need it on 64-bit platforms.
#endif // __POINTER_WIDTH__ == 32
