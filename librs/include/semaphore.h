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
 * POSIX unnamed semaphores.
 *
 * newlib 4.4.0 does not ship <semaphore.h> at all, even though the kernel
 * implements the whole sem_* family (in librs/src/semaphore/mod.rs). A C
 * program therefore had no way to declare a `sem_t`, let alone call
 * sem_init().
 *
 * The type here is the kernel's own: a single counter. The `libc` crate's
 * `sem_t` describes the Linux type, which is a 16/32-byte union reserved for
 * the futex-based Linux implementation; using it would make the kernel write
 * past the end of the caller's object. The size is pinned by the
 * _Static_assert below and by the matching assertion in
 * librs/src/pthread.rs.
 */

#ifndef LIBRS_INCLUDE_SEMAPHORE_H
#define LIBRS_INCLUDE_SEMAPHORE_H

#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <sys/types.h>
#include <time.h>

#ifdef __cplusplus
extern "C" {
#endif

/* The kernel's semaphore is one machine word wide. */
typedef struct {
  unsigned long __count;
} sem_t;

/*
 * The layout has to match `RsSemaphore` in librs exactly, because the
 * kernel casts the caller's pointer to that type.
 */
_Static_assert(sizeof(sem_t) == sizeof(unsigned long),
               "sem_t does not match the kernel's semaphore object");
_Static_assert(_Alignof(sem_t) == _Alignof(unsigned long),
               "sem_t does not match the kernel's semaphore alignment");

#define SEM_FAILED ((sem_t *)-1)

#define SEM_VALUE_MAX UINT_MAX

int sem_init(sem_t *sem, int pshared, unsigned int value);
int sem_destroy(sem_t *sem);
int sem_close(sem_t *sem);
int sem_getvalue(sem_t *sem, int *sval);
int sem_post(sem_t *sem);
int sem_wait(sem_t *sem);
int sem_trywait(sem_t *sem);

/* POSIX: waits until the absolute deadline on CLOCK_REALTIME passes. */
int sem_timedwait(sem_t *sem, const struct timespec *abs_timeout);

/* Issue 8: the deadline may be on any clock the kernel implements. */
int sem_clockwait(sem_t *sem, clockid_t clock_id,
                  const struct timespec *abs_timeout);

#ifdef __cplusplus
}
#endif

#endif /* LIBRS_INCLUDE_SEMAPHORE_H */
