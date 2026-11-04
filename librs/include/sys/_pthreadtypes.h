/*
 * Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *       http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * <sys/_pthreadtypes.h> for BlueKernel.
 *
 * Why this file overrides newlib's
 * -------------------------------
 * newlib describes the POSIX synchronization objects as four-byte
 * identifiers:
 *
 *   typedef __uint32_t pthread_mutex_t;
 *   typedef __uint32_t pthread_cond_t;
 *   typedef __uint32_t pthread_rwlock_t;
 *
 * That is newlib's own implementation strategy - it keeps the objects in a
 * process-wide table and hands out indices. This kernel does not: the objects
 * live in librs/src/sync/ and they are the real thing (a mutex is a lock word
 * plus a recursive counter plus a type).
 *
 * The two representations cannot be mixed. A C program that declares a
 * `pthread_mutex_t` with newlib's header allocates four bytes, and the
 * kernel then writes a 24-byte mutex object into it - overwriting whatever
 * the caller had next to it on the stack. That is not a portability
 * annoyance, it is silent memory corruption, and it happens in every
 * program that uses a mutex.
 *
 * Overriding *this* header rather than <pthread.h> is the only way to fix
 * it. newlib's <sys/types.h> includes <sys/_pthreadtypes.h> unconditionally,
 * so a C translation unit that includes <errno.h> (and therefore
 * <sys/types.h>) gets newlib's four-byte typedefs before it ever reaches
 * <pthread.h>. A replacement <pthread.h> cannot undo that: the typedefs are
 * already in place and the second definition is a hard error
 * ("typedef redefinition with different types"). Replacing the header that
 * actually defines them does fix it, and -I precedes -isystem on both
 * compilers, so this file is the one that gets picked up.
 *
 * The types below are sized and aligned to match the kernel's objects. The
 * sizes are pinned by the _Static_asserts at the bottom of this file and by
 * the matching assertions in librs/src/sync/abi.rs, so a change on either
 * side that breaks the agreement fails the build instead of corrupting
 * memory at run time.
 *
 * The objects are opaque to the C caller: the layout below only has to be
 * large enough and aligned enough to hold the kernel's object. The attribute
 * types are the exception - the caller sets fields in them - so their
 * layout is spelled out.
 */

#ifndef _SYS__PTHREADTYPES_H_
#define _SYS__PTHREADTYPES_H_

/* The C library's thread identifier. */
typedef unsigned int pthread_t;

/* The C library's thread-specific storage key. */
typedef unsigned int pthread_key_t;

/*
 * The once-control object.
 *
 * Two ints: whether the object has been initialized, and whether the
 * initializer has already run. The kernel reads the second one to decide
 * whether the initializer still has to be called.
 */
typedef struct {
  int __is_initialized;
  int __init_executed;
} pthread_once_t;

/*
 * The statically initialised forms.
 *
 * The kernel's objects are not a magic sentinel value, so a statically
 * initialised object has to start out in the state the kernel expects: an
 * unlocked mutex, a condition variable with no waiters, a reader/writer
 * lock nobody holds. All of those are the all-zero bit pattern, so the
 * initializers below are simply "all zeroes".
 */
#define _PTHREAD_MUTEX_INITIALIZER {{0}}
#define _PTHREAD_COND_INITIALIZER {{0}}
#define _PTHREAD_RWLOCK_INITIALIZER {{0}}
#define _PTHREAD_ONCE_INIT {0, 0}

/* Whether a thread is joinable or detached. */
#define PTHREAD_CREATE_JOINABLE 0
#define PTHREAD_CREATE_DETACHED 1

/* Scheduling scope and inheritance. */
#define PTHREAD_SCOPE_PROCESS 0
#define PTHREAD_SCOPE_SYSTEM 1
#define PTHREAD_INHERIT_SCHED 1
#define PTHREAD_EXPLICIT_SCHED 2

/* Whether a synchronization object is shared between processes. */
#define PTHREAD_PROCESS_PRIVATE 0
#define PTHREAD_PROCESS_SHARED 1

/* Mutex types. These are the values the kernel understands; they are not
 * the ones newlib's header uses, and they have to match the constants in
 * the libc crate (libc/src/unix/newlib/blueos/mod.rs) because that is what
 * the Rust implementation matches on. */
#define PTHREAD_MUTEX_NORMAL 0
#define PTHREAD_MUTEX_RECURSIVE 1
#define PTHREAD_MUTEX_ERRORCHECK 2
#define PTHREAD_MUTEX_DEFAULT PTHREAD_MUTEX_NORMAL

/* Robust mutexes. */
#define PTHREAD_MUTEX_STALLED 0
#define PTHREAD_MUTEX_ROBUST 1

/* Priority protection protocols. */
#define PTHREAD_PRIO_NONE 0
#define PTHREAD_PRIO_INHERIT 1
#define PTHREAD_PRIO_PROTECT 2

/*
 * The opaque objects.
 *
 * The kernel's mutex is a lock word, a recursive counter, a type byte and a
 * robust flag (24 bytes on a 64-bit target); its condition variable is two
 * counters plus the clock its deadlines are measured on (24 bytes); its
 * reader/writer lock is one state word (8 bytes); its barrier is a count, a
 * generation counter, a mutex and a condition variable (48 bytes).
 */
typedef union {
  long __opaque[3];
} pthread_mutex_t;

typedef union {
  long __opaque[3];
} pthread_cond_t;

typedef union {
  long __opaque[1];
} pthread_rwlock_t;

typedef union {
  long __opaque[6];
} pthread_barrier_t;

typedef union {
  int __opaque[1];
} pthread_spinlock_t;

/*
 * The attribute types are not opaque: the caller sets fields in them and
 * the kernel reads them, so their layout has to match exactly.
 *
 * pthread_mutexattr_t is five ints: the priority ceiling, the protocol,
 * the pshared flag, the robust flag and the type.
 */
typedef struct {
  int __prioceiling;
  int __protocol;
  int __pshared;
  int __robust;
  int __type;
} pthread_mutexattr_t;

/* pthread_condattr_t is the clock id and the pshared flag. */
typedef struct {
  clockid_t __clock;
  int __pshared;
} pthread_condattr_t;

/* pthread_rwlockattr_t is the pshared flag. */
typedef struct {
  int __pshared;
} pthread_rwlockattr_t;

/* pthread_barrierattr_t is the pshared flag. */
typedef struct {
  int __pshared;
} pthread_barrierattr_t;

/*
 * pthread_attr_t: the stack size plus the room the kernel keeps for the
 * other attributes.
 */
typedef struct {
  size_t __stack_size;
  size_t __reserved[4];
} pthread_attr_t;

/*
 * The sizes have to match the kernel's objects exactly, because the kernel
 * casts the caller's pointer to its own type.
 */
_Static_assert(sizeof(pthread_mutex_t) == 24 && _Alignof(pthread_mutex_t) == 8,
               "pthread_mutex_t does not match the kernel's mutex object");
_Static_assert(sizeof(pthread_cond_t) == 24 && _Alignof(pthread_cond_t) == 8,
               "pthread_cond_t does not match the kernel's condition variable");
_Static_assert(sizeof(pthread_rwlock_t) == 8 && _Alignof(pthread_rwlock_t) == 8,
               "pthread_rwlock_t does not match the kernel's reader/writer lock");
_Static_assert(sizeof(pthread_barrier_t) == 48 && _Alignof(pthread_barrier_t) == 8,
               "pthread_barrier_t does not match the kernel's barrier");
_Static_assert(sizeof(pthread_spinlock_t) == 4,
               "pthread_spinlock_t does not match the kernel's spin lock");
_Static_assert(sizeof(pthread_mutexattr_t) == 20,
               "pthread_mutexattr_t does not match the kernel's attributes");
_Static_assert(offsetof(pthread_condattr_t, __pshared) == sizeof(clockid_t),
               "pthread_condattr_t does not match the kernel's attributes");
_Static_assert(sizeof(pthread_rwlockattr_t) == 4,
               "pthread_rwlockattr_t does not match the kernel's attributes");
_Static_assert(sizeof(pthread_barrierattr_t) == 4,
               "pthread_barrierattr_t does not match the kernel's attributes");
_Static_assert(sizeof(pthread_attr_t) == 5 * sizeof(size_t),
               "pthread_attr_t does not match the kernel's attributes");

#endif /* !_SYS__PTHREADTYPES_H_ */
