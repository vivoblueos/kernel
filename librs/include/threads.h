/*-
 * Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
 * SPDX-License-Identifier: Apache-2.0
 *
 * C11 <threads.h> for BlueOS. The bundled newlib ships a <threads.h> that
 * includes <machine/_threads.h>, which does not exist in this toolchain, and
 * its libc.a carries none of the thrd_/mtx_/cnd_/tss_/call_once symbols. This
 * header replaces it; the implementations live in librs (see
 * librs/src/threads.rs) on top of the pthread layer.
 *
 * The types are plain aliases of the pthread types, so the Rust side sees
 * exactly the objects a C caller passes - no layout negotiation.
 */

#ifndef _BLUEOS_THREADS_H_
#define _BLUEOS_THREADS_H_

#include <pthread.h>
#include <time.h>

typedef void (*tss_dtor_t)(void *);
typedef int (*thrd_start_t)(void *);

/* C11 result codes. */
enum {
    thrd_busy = 1,
    thrd_error = 2,
    thrd_nomem = 3,
    thrd_success = 4,
    thrd_timedout = 5
};

/* C11 mutex type bit flags. */
enum {
    mtx_plain = 0x1,
    mtx_recursive = 0x2,
    mtx_timed = 0x4
};

typedef pthread_t thrd_t;
typedef pthread_key_t tss_t;

/*
 * mtx_t / cnd_t CANNOT alias newlib's pthread_mutex_t / pthread_cond_t: those
 * are single 32-bit ids, while the implementations in librs store real
 * synchronization objects in them (a 24-byte 8-aligned Mutex, a 24-byte
 * 8-aligned Cond). Alias them and a C caller's storage is overrun. The static
 * asserts pin both sides; if they drift, the Rust build fails first.
 */
/* Sizes follow the pointer width, matching librs/src/threads.rs. */
#if __SIZEOF_POINTER__ == 8
typedef struct {
    unsigned char _opaque[24];
} __attribute__((aligned(8))) mtx_t;

typedef struct {
    unsigned char _opaque[24];
} __attribute__((aligned(8))) cnd_t;

_Static_assert(sizeof(mtx_t) == 24 && _Alignof(mtx_t) == 8,
               "mtx_t must match the Rust Mutex layout");
_Static_assert(sizeof(cnd_t) == 24 && _Alignof(cnd_t) == 8,
               "cnd_t must match the Rust Cond layout");
#else
typedef struct {
    unsigned char _opaque[12];
} __attribute__((aligned(4))) mtx_t;

typedef struct {
    unsigned char _opaque[16];
} __attribute__((aligned(8))) cnd_t;

_Static_assert(sizeof(mtx_t) == 12 && _Alignof(mtx_t) == 4,
               "mtx_t must match the Rust Mutex layout");
_Static_assert(sizeof(cnd_t) == 16 && _Alignof(cnd_t) == 8,
               "cnd_t must match the Rust Cond layout");
#endif

#ifndef __cplusplus
#define thread_local _Thread_local
#endif

/* once_flag starts zeroed; call_once drives its state machine. */
typedef struct {
    unsigned long _state;
} once_flag;

#ifdef __cplusplus
extern "C" {
#endif

void call_once(once_flag *, void (*)(void));
int cnd_broadcast(cnd_t *);
void cnd_destroy(cnd_t *);
int cnd_init(cnd_t *);
int cnd_signal(cnd_t *);
int cnd_timedwait(cnd_t *__restrict, mtx_t *__restrict,
                  const struct timespec *__restrict);
int cnd_wait(cnd_t *, mtx_t *);
void mtx_destroy(mtx_t *);
int mtx_init(mtx_t *, int);
int mtx_lock(mtx_t *);
int mtx_timedlock(mtx_t *__restrict, const struct timespec *__restrict);
int mtx_trylock(mtx_t *);
int mtx_unlock(mtx_t *);
int thrd_create(thrd_t *, thrd_start_t, void *);
thrd_t thrd_current(void);
int thrd_detach(thrd_t);
int thrd_equal(thrd_t, thrd_t);
_Noreturn void thrd_exit(int);
int thrd_join(thrd_t, int *);
int thrd_sleep(const struct timespec *, struct timespec *);
void thrd_yield(void);
int tss_create(tss_t *, tss_dtor_t);
void tss_delete(tss_t);
void *tss_get(tss_t);
int tss_set(tss_t, void *);

#ifdef __cplusplus
}
#endif

#endif /* !_BLUEOS_THREADS_H_ */
