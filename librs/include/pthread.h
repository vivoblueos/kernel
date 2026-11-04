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
 * <pthread.h> for BlueKernel.
 *
 * The types live in <sys/_pthreadtypes.h>, not here.
 *
 * newlib describes the POSIX synchronization objects as four-byte
 * identifiers:
 *
 *   typedef __uint32_t pthread_mutex_t;
 *
 * That is newlib's own implementation strategy - it keeps the objects in a
 * process-wide table and hands out indices. This kernel does not: the
 * objects live in librs/src/sync/ and they are the real thing (a mutex is
 * a lock word plus a recursive counter plus a type).
 *
 * The two representations cannot be mixed. A C program that declares a
 * `pthread_mutex_t` with newlib's header allocates four bytes, and the
 * kernel then writes a 24-byte mutex object into it - overwriting whatever
 * the caller had next to it on the stack. That is silent memory
 * corruption, and it happens in every program that uses a mutex.
 *
 * Replacing <pthread.h> alone does not fix that. newlib's <sys/types.h>
 * includes <sys/_pthreadtypes.h> unconditionally, so a translation unit
 * that includes <errno.h> (and therefore <sys/types.h>) gets newlib's
 * four-byte typedefs before it ever reaches <pthread.h>; a second
 * definition is a hard error. The header that actually defines the types
 * is therefore replaced instead - see librs/include/sys/_pthreadtypes.h,
 * which also explains the layout in detail.
 *
 * This file therefore only declares the functions. The sizes and
 * alignments are pinned by the _Static_asserts in
 * librs/include/sys/_pthreadtypes.h and by the matching assertions in
 * librs/src/sync/abi.rs, so a change on either side that breaks the
 * agreement fails the build instead of corrupting memory at run time.
 */

#ifndef LIBRS_INCLUDE_PTHREAD_H
#define LIBRS_INCLUDE_PTHREAD_H

#include <limits.h>
#include <sched.h>
#include <stddef.h>
#include <sys/types.h>
#include <time.h>

#ifdef __cplusplus
extern "C" {
#endif

/* The statically initialised forms. */
#define PTHREAD_MUTEX_INITIALIZER _PTHREAD_MUTEX_INITIALIZER
#define PTHREAD_COND_INITIALIZER _PTHREAD_COND_INITIALIZER
#define PTHREAD_RWLOCK_INITIALIZER _PTHREAD_RWLOCK_INITIALIZER
#define PTHREAD_ONCE_INIT _PTHREAD_ONCE_INIT

#define PTHREAD_CANCEL_ENABLE 0
#define PTHREAD_CANCEL_DISABLE 1
#define PTHREAD_CANCEL_DEFERRED 0
#define PTHREAD_CANCEL_ASYNCHRONOUS 1
#define PTHREAD_CANCELED ((void *) -1)

#define PTHREAD_BARRIER_SERIAL_THREAD (-1)

/* --- Threads --- */
int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start_routine)(void *), void *arg);
int pthread_join(pthread_t thread, void **retval);
int pthread_detach(pthread_t thread);
pthread_t pthread_self(void);
int pthread_equal(pthread_t t1, pthread_t t2);
void pthread_exit(void *retval);
int pthread_cancel(pthread_t thread);
int pthread_testcancel(void);
int pthread_setcancelstate(int state, int *oldstate);
int pthread_setcanceltype(int type, int *oldtype);
int pthread_getconcurrency(void);
int pthread_setconcurrency(int level);
int pthread_getschedparam(pthread_t thread, int *policy,
                           struct sched_param *param);
int pthread_setschedparam(pthread_t thread, int policy,
                           const struct sched_param *param);
int pthread_setschedprio(pthread_t thread, int prio);
int pthread_getcpuclockid(pthread_t thread, clockid_t *clockid);
int pthread_set_name_np(pthread_t thread, const char *name);

/* --- Thread-specific storage --- */
int pthread_key_create(pthread_key_t *key, void (*destructor)(void *));
int pthread_key_delete(pthread_key_t key);
void *pthread_getspecific(pthread_key_t key);
int pthread_setspecific(pthread_key_t key, const void *value);

/* --- Dynamic initialization --- */
int pthread_once(pthread_once_t *once_control, void (*init_routine)(void));

/* --- Mutexes --- */
int pthread_mutex_init(pthread_mutex_t *mutex, const pthread_mutexattr_t *attr);
int pthread_mutex_destroy(pthread_mutex_t *mutex);
int pthread_mutex_lock(pthread_mutex_t *mutex);
int pthread_mutex_trylock(pthread_mutex_t *mutex);
int pthread_mutex_unlock(pthread_mutex_t *mutex);
int pthread_mutex_timedlock(pthread_mutex_t *mutex,
                            const struct timespec *abstime);
/* Issue 8: the deadline may be on any clock the kernel implements. */
int pthread_mutex_clocklock(pthread_mutex_t *mutex, clockid_t clock_id,
                             const struct timespec *abstime);
int pthread_mutexattr_init(pthread_mutexattr_t *attr);
int pthread_mutexattr_destroy(pthread_mutexattr_t *attr);
int pthread_mutexattr_settype(pthread_mutexattr_t *attr, int type);
int pthread_mutexattr_gettype(const pthread_mutexattr_t *attr, int *type);
int pthread_mutexattr_setpshared(pthread_mutexattr_t *attr, int pshared);
int pthread_mutexattr_getpshared(const pthread_mutexattr_t *attr,
                                 int *pshared);
int pthread_mutexattr_setrobust(pthread_mutexattr_t *attr, int robust);
int pthread_mutexattr_getrobust(const pthread_mutexattr_t *attr, int *robust);
int pthread_mutexattr_setprioceiling(pthread_mutexattr_t *attr, int ceiling);
int pthread_mutexattr_getprioceiling(const pthread_mutexattr_t *attr,
                                     int *ceiling);
int pthread_mutexattr_setprotocol(pthread_mutexattr_t *attr, int protocol);
int pthread_mutexattr_getprotocol(const pthread_mutexattr_t *attr,
                                  int *protocol);

/* --- Condition variables --- */
int pthread_cond_init(pthread_cond_t *cond, const pthread_condattr_t *attr);
int pthread_cond_destroy(pthread_cond_t *cond);
int pthread_cond_signal(pthread_cond_t *cond);
int pthread_cond_broadcast(pthread_cond_t *cond);
int pthread_cond_wait(pthread_cond_t *cond, pthread_mutex_t *mutex);
int pthread_cond_timedwait(pthread_cond_t *cond, pthread_mutex_t *mutex,
                           const struct timespec *abstime);
/* Issue 8: the deadline may be on any clock the kernel implements. */
int pthread_cond_clockwait(pthread_cond_t *cond, pthread_mutex_t *mutex,
                           clockid_t clock_id,
                           const struct timespec *abstime);
int pthread_condattr_init(pthread_condattr_t *attr);
int pthread_condattr_destroy(pthread_condattr_t *attr);
int pthread_condattr_setclock(pthread_condattr_t *attr, clockid_t clock_id);
int pthread_condattr_getclock(const pthread_condattr_t *attr,
                               clockid_t *clock_id);
int pthread_condattr_setpshared(pthread_condattr_t *attr, int pshared);
int pthread_condattr_getpshared(const pthread_condattr_t *attr, int *pshared);

/* --- Reader/writer locks --- */
int pthread_rwlock_init(pthread_rwlock_t *rwlock,
                         const pthread_rwlockattr_t *attr);
int pthread_rwlock_destroy(pthread_rwlock_t *rwlock);
int pthread_rwlock_rdlock(pthread_rwlock_t *rwlock);
int pthread_rwlock_tryrdlock(pthread_rwlock_t *rwlock);
int pthread_rwlock_wrlock(pthread_rwlock_t *rwlock);
int pthread_rwlock_trywrlock(pthread_rwlock_t *rwlock);
int pthread_rwlock_unlock(pthread_rwlock_t *rwlock);
int pthread_rwlock_timedrdlock(pthread_rwlock_t *rwlock,
                               const struct timespec *abstime);
int pthread_rwlock_timedwrlock(pthread_rwlock_t *rwlock,
                               const struct timespec *abstime);
/* Issue 8: the deadline may be on any clock the kernel implements. */
int pthread_rwlock_clockrdlock(pthread_rwlock_t *rwlock, clockid_t clock_id,
                                const struct timespec *abstime);
int pthread_rwlock_clockwrlock(pthread_rwlock_t *rwlock, clockid_t clock_id,
                                const struct timespec *abstime);
int pthread_rwlockattr_init(pthread_rwlockattr_t *attr);
int pthread_rwlockattr_destroy(pthread_rwlockattr_t *attr);
int pthread_rwlockattr_setpshared(pthread_rwlockattr_t *attr, int pshared);
int pthread_rwlockattr_getpshared(const pthread_rwlockattr_t *attr,
                                  int *pshared);

/* --- Barriers --- */
int pthread_barrier_init(pthread_barrier_t *barrier,
                          const pthread_barrierattr_t *attr,
                          unsigned count);
int pthread_barrier_destroy(pthread_barrier_t *barrier);
int pthread_barrier_wait(pthread_barrier_t *barrier);
int pthread_barrierattr_init(pthread_barrierattr_t *attr);
int pthread_barrierattr_destroy(pthread_barrierattr_t *attr);
int pthread_barrierattr_setpshared(pthread_barrierattr_t *attr, int pshared);
int pthread_barrierattr_getpshared(const pthread_barrierattr_t *attr,
                                   int *pshared);

/* --- Spin locks --- */
int pthread_spin_init(pthread_spinlock_t *lock, int pshared);
int pthread_spin_destroy(pthread_spinlock_t *lock);
int pthread_spin_lock(pthread_spinlock_t *lock);
int pthread_spin_trylock(pthread_spinlock_t *lock);
int pthread_spin_unlock(pthread_spinlock_t *lock);

/* --- Thread attributes --- */
int pthread_attr_init(pthread_attr_t *attr);
int pthread_attr_destroy(pthread_attr_t *attr);
int pthread_attr_setstacksize(pthread_attr_t *attr, size_t stacksize);
int pthread_attr_getstacksize(const pthread_attr_t *attr, size_t *stacksize);

#ifdef __cplusplus
}
#endif

#endif /* LIBRS_INCLUDE_PTHREAD_H */
