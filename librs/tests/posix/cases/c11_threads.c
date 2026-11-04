/*-
 * Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
 * SPDX-License-Identifier: Apache-2.0
 *
 * C11 <threads.h>: POSIX.1-2024 (Issue 8) makes all 25 interfaces required.
 * Exercises thrd_/mtx_/cnd_/tss_/call_once through the C ABI against the
 * Rust implementation in librs/src/threads.rs.
 */

#include <pthread.h>
#include <threads.h>
#include <time.h>

#include "posix_case.h"



#define THRD_TIMEOUT_NS (1000 * 1000 * 1000)

static void nap_ms(long ms) {
  struct timespec t = {ms / 1000, (ms % 1000) * 1000 * 1000};
  nanosleep(&t, NULL);
}

static void deadline_in_ms(struct timespec *d, long ms) {
  clock_gettime(CLOCK_REALTIME, d);
  d->tv_nsec += ms * 1000 * 1000;
  while (d->tv_nsec >= THRD_TIMEOUT_NS) {
    d->tv_sec += 1;
    d->tv_nsec -= THRD_TIMEOUT_NS;
  }
}

/* ------------------------------------------------------------------ */
/* thrd_create / thrd_join / thrd_exit / thrd_equal / thrd_current    */
/* ------------------------------------------------------------------ */

static int seen_value;

static int add_arg(void *arg) {
  seen_value = (int)(intptr_t)arg;
  return 42;
}

static int exit_7(void *unused) {
  (void)unused;
  thrd_exit(7); /* _Noreturn; control never reaches here */
}

static int self_check(void *arg) {
  thrd_t self = *(thrd_t *)arg;
  if (!thrd_equal(thrd_current(), self)) {
    return 1;
  }
  return 3;
}

static int sleeper(void *arg) {
  (void)arg;
  nap_ms(20);
  return 0;
}

static int case_thread_lifecycle(void) {
  thrd_t t;
  int res = -1;

  /* create + join with a return value and an argument. */
  POSIX_ASSERT_EQ(thrd_create(&t, add_arg, (void *)(intptr_t)123), thrd_success);
  POSIX_ASSERT(!thrd_equal(t, thrd_current()));
  POSIX_ASSERT_EQ(thrd_join(t, &res), thrd_success);
  POSIX_ASSERT_EQ(res, 42);
  POSIX_ASSERT_EQ(seen_value, 123);

  /* thrd_exit from a _Noreturn start function. */
  res = -1;
  POSIX_ASSERT_EQ(thrd_create(&t, exit_7, NULL), thrd_success);
  POSIX_ASSERT_EQ(thrd_join(t, &res), thrd_success);
  POSIX_ASSERT_EQ(res, 7);

  /* thrd_current inside the thread. */
  POSIX_ASSERT_EQ(thrd_create(&t, self_check, &t), thrd_success);
  POSIX_ASSERT_EQ(thrd_join(t, &res), thrd_success);
  POSIX_ASSERT_EQ(res, 3);

  /* Detached thread: keep it alive long enough that detach races neither
     with its exit nor with the join path. POSIX only makes double-detach a
     "may fail", so the second call's result is unspecified. */
  POSIX_ASSERT_EQ(thrd_create(&t, sleeper, NULL), thrd_success);
  POSIX_ASSERT_EQ(thrd_detach(t), thrd_success);
  (void)thrd_detach(t);
  nap_ms(30);

  /* Joining a bogus handle must fail. */
  POSIX_ASSERT(thrd_join((thrd_t)0xdeadbeef, NULL) != thrd_success);

  return POSIX_PASS;
}

/* ------------------------------------------------------------------ */
/* mtx_*                                                              */
/* ------------------------------------------------------------------ */

static mtx_t plain_mutex;
static int guarded;

static int plain_locker(void *arg) {
  (void)arg;
  for (int i = 0; i < 100; i++) {
    /* The counter is the shared data the mutex must protect: `guarded++`
       has to run inside the critical section, not after the unlock. Left
       outside, the read-modify-write races on SMP and the "must stay exact"
       check below loses updates (observed as 199 on qemu_riscv64). */
    if (mtx_lock(&plain_mutex) != thrd_success) {
      return 1;
    }
    guarded++;
    if (mtx_unlock(&plain_mutex) != thrd_success) {
      return 1;
    }
  }
  return 0;
}

static int case_mutex_basics(void) {
  POSIX_ASSERT_EQ(mtx_init(&plain_mutex, mtx_plain), thrd_success);

  /* Contended locking across two threads; the counter must stay exact. */
  guarded = 0;
  thrd_t a, b;
  POSIX_ASSERT_EQ(thrd_create(&a, plain_locker, NULL), thrd_success);
  POSIX_ASSERT_EQ(thrd_create(&b, plain_locker, NULL), thrd_success);
  POSIX_ASSERT_EQ(thrd_join(a, NULL), thrd_success);
  POSIX_ASSERT_EQ(thrd_join(b, NULL), thrd_success);
  POSIX_ASSERT_EQ(guarded, 200);

  /* trylock on a held mutex reports busy, unlock clears it. */
  POSIX_ASSERT_EQ(mtx_lock(&plain_mutex), thrd_success);
  POSIX_ASSERT_EQ(mtx_trylock(&plain_mutex), thrd_busy);
  POSIX_ASSERT_EQ(mtx_unlock(&plain_mutex), thrd_success);
  POSIX_ASSERT_EQ(mtx_trylock(&plain_mutex), thrd_success);
  POSIX_ASSERT_EQ(mtx_unlock(&plain_mutex), thrd_success);
  mtx_destroy(&plain_mutex);

  mtx_t rec;
  POSIX_ASSERT_EQ(mtx_init(&rec, mtx_recursive), thrd_success);
  POSIX_ASSERT_EQ(mtx_lock(&rec), thrd_success);
  POSIX_ASSERT_EQ(mtx_lock(&rec), thrd_success);
  POSIX_ASSERT_EQ(mtx_unlock(&rec), thrd_success);
  POSIX_ASSERT_EQ(mtx_unlock(&rec), thrd_success);
  mtx_destroy(&rec);

  mtx_t timed;
  POSIX_ASSERT_EQ(mtx_init(&timed, mtx_timed), thrd_success);
  POSIX_ASSERT_EQ(mtx_lock(&timed), thrd_success);
  struct timespec deadline;
  deadline_in_ms(&deadline, 30);
  POSIX_ASSERT_EQ(mtx_timedlock(&timed, &deadline), thrd_timedout);
  POSIX_ASSERT_EQ(mtx_unlock(&timed), thrd_success);
  deadline_in_ms(&deadline, 10000);
  POSIX_ASSERT_EQ(mtx_timedlock(&timed, &deadline), thrd_success);
  POSIX_ASSERT_EQ(mtx_unlock(&timed), thrd_success);
  mtx_destroy(&timed);

  mtx_t bad;
  POSIX_ASSERT_EQ(mtx_init(&bad, 0), thrd_error);
  POSIX_ASSERT_EQ(mtx_init(&bad, 0x8), thrd_error);

  return POSIX_PASS;
}

/* ------------------------------------------------------------------ */
/* cnd_*                                                              */
/* ------------------------------------------------------------------ */

static mtx_t cond_mutex;
static cnd_t cond;
static int cond_stage;

static int waiter(void *arg) {
  (void)arg;
  if (mtx_lock(&cond_mutex) != thrd_success) {
    return 1;
  }
  while (cond_stage < 1) {
    if (cnd_wait(&cond, &cond_mutex) != thrd_success) {
      return 1;
    }
  }
  cond_stage = 2;
  if (mtx_unlock(&cond_mutex) != thrd_success) {
    return 1;
  }
  return 0;
}

static int timeout_waiter(void *arg) {
  (void)arg;
  struct timespec deadline;
  deadline_in_ms(&deadline, 20);
  if (mtx_lock(&cond_mutex) != thrd_success) {
    return 1;
  }
  if (cnd_timedwait(&cond, &cond_mutex, &deadline) != thrd_timedout) {
    return 1;
  }
  if (mtx_unlock(&cond_mutex) != thrd_success) {
    return 1;
  }
  return 0;
}

static int case_cond_basics(void) {
  POSIX_ASSERT_EQ(mtx_init(&cond_mutex, mtx_plain), thrd_success);
  POSIX_ASSERT_EQ(cnd_init(&cond), thrd_success);

  /* Signal path: waiter blocks, signal wakes it, it flips the stage. */
  cond_stage = 0;
  thrd_t t;
  POSIX_ASSERT_EQ(thrd_create(&t, waiter, NULL), thrd_success);
  /* Give the waiter time to enter cnd_wait, then flip the stage under the
     mutex and signal. The mutex handoff makes the wakeup lossless. */
  nap_ms(20);
  POSIX_ASSERT_EQ(mtx_lock(&cond_mutex), thrd_success);
  cond_stage = 1;
  POSIX_ASSERT_EQ(cnd_signal(&cond), thrd_success);
  POSIX_ASSERT_EQ(mtx_unlock(&cond_mutex), thrd_success);
  POSIX_ASSERT_EQ(thrd_join(t, NULL), thrd_success);
  POSIX_ASSERT_EQ(cond_stage, 2);

  /* Broadcast with no waiters is legal and must not hang. */
  POSIX_ASSERT_EQ(cnd_broadcast(&cond), thrd_success);

  /* Timedwait timeout path. */
  POSIX_ASSERT_EQ(thrd_create(&t, timeout_waiter, NULL), thrd_success);
  POSIX_ASSERT_EQ(thrd_join(t, NULL), thrd_success);

  cnd_destroy(&cond);
  mtx_destroy(&cond_mutex);
  return POSIX_PASS;
}

/* ------------------------------------------------------------------ */
/* tss_*                                                              */
/* ------------------------------------------------------------------ */

static tss_t counter_key;

static int tss_worker(void *arg) {
  intptr_t base = (intptr_t)arg;
  if (tss_set(counter_key, (void *)(base + 1)) != thrd_success) {
    return 1;
  }
  /* Give another thread a chance to write its own slot; ours must not
     move - that is the whole point of thread-specific storage. */
  nap_ms(2);
  if ((intptr_t)tss_get(counter_key) != base + 1) {
    return 1;
  }
  return 0;
}

static int case_tss_basics(void) {
  POSIX_ASSERT_EQ(tss_create(&counter_key, NULL), thrd_success);
  POSIX_ASSERT(tss_get(counter_key) == NULL);
  POSIX_ASSERT_EQ(tss_set(counter_key, (void *)(intptr_t)77), thrd_success);
  POSIX_ASSERT_EQ((intptr_t)tss_get(counter_key), 77);

  thrd_t a, b;
  POSIX_ASSERT_EQ(thrd_create(&a, tss_worker, (void *)(intptr_t)100), thrd_success);
  POSIX_ASSERT_EQ(thrd_create(&b, tss_worker, (void *)(intptr_t)200), thrd_success);
  POSIX_ASSERT_EQ(thrd_join(a, NULL), thrd_success);
  POSIX_ASSERT_EQ(thrd_join(b, NULL), thrd_success);
  POSIX_ASSERT_EQ((intptr_t)tss_get(counter_key), 77);
  tss_delete(counter_key);
  return POSIX_PASS;
}

/* ------------------------------------------------------------------ */
/* call_once                                                          */
/* ------------------------------------------------------------------ */

static once_flag once = {0};
static int once_runs;

static void init_once(void) { once_runs++; }

static int once_caller(void *arg) {
  (void)arg;
  call_once(&once, init_once);
  return 0;
}

static int case_call_once(void) {
  once_runs = 0;
  thrd_t a, b, c;
  POSIX_ASSERT_EQ(thrd_create(&a, once_caller, NULL), thrd_success);
  POSIX_ASSERT_EQ(thrd_create(&b, once_caller, NULL), thrd_success);
  POSIX_ASSERT_EQ(thrd_create(&c, once_caller, NULL), thrd_success);
  POSIX_ASSERT_EQ(thrd_join(a, NULL), thrd_success);
  POSIX_ASSERT_EQ(thrd_join(b, NULL), thrd_success);
  POSIX_ASSERT_EQ(thrd_join(c, NULL), thrd_success);
  call_once(&once, init_once); /* must be a no-op now */
  POSIX_ASSERT_EQ(once_runs, 1);
  return POSIX_PASS;
}

/* ------------------------------------------------------------------ */

static int case_thrd_misc(void) {
  /* thrd_sleep: ~10ms, must return 0 and leave no remainder. */
  struct timespec req = {0, 10 * 1000 * 1000}, rem = {0, 0};
  POSIX_ASSERT_EQ(thrd_sleep(&req, &rem), 0);
  POSIX_ASSERT(rem.tv_sec == 0 && rem.tv_nsec == 0);

  thrd_yield(); /* must simply not hang */
  return POSIX_PASS;
}

POSIX_CASE("c11_thrd_lifecycle", case_thread_lifecycle);
POSIX_CASE("c11_mtx", case_mutex_basics);
POSIX_CASE("c11_cnd", case_cond_basics);
POSIX_CASE("c11_tss", case_tss_basics);
POSIX_CASE("c11_call_once", case_call_once);
POSIX_CASE("c11_thrd_misc", case_thrd_misc);
