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
 * The Issue 8 clock-aware interfaces: timespec_get(), sem_clockwait(),
 * pthread_cond_clockwait(), pthread_mutex_clocklock() and the two
 * pthread_rwlock_clock* variants.
 *
 * Every one of these takes an absolute deadline on a caller-chosen clock.
 * That is the part worth testing: the kernel's futex wants a *relative*
 * timeout, so a deadline that is passed through unconverted makes the wait
 * either return immediately or hang forever. A test that only checks the
 * happy path would not notice - the deadline has to be in the past to see
 * the difference.
 *
 * Two conventions matter for the assertions below, and both are easy to get
 * wrong:
 *
 *   - The pthread interfaces return the error number itself ("otherwise, an
 *     error number shall be returned"), so a timeout is ETIMEDOUT, not -1
 *     with errno set. The sem_* family is the other way round: -1 plus
 *     errno.
 *
 *   - POSIX says a timed lock "shall not fail with a timeout if the lock
 *     can be acquired immediately", and that "the validity of the abstime
 *     parameter need not be checked if the lock can be locked immediately".
 *     A timeout can therefore only be provoked on a lock that is actually
 *     held by another thread.
 */

#include <errno.h>
#include <pthread.h>
#include <semaphore.h>
#include <stddef.h>
#include <threads.h>
#include <time.h>

#include "posix_case.h"
#include "posix_issue8.h"

/* A deadline that has certainly passed by the time it is used. */
static struct timespec past_deadline(void) {
  struct timespec ts;
  if (clock_gettime(CLOCK_REALTIME, &ts) != 0) {
    ts.tv_sec = 0;
    ts.tv_nsec = 0;
  }
  /* Two seconds in the past: no clock adjustment in between can undo it. */
  ts.tv_sec -= 2;
  return ts;
}

/* A deadline far enough in the future that it cannot expire. */
static struct timespec future_deadline(void) {
  struct timespec ts;
  if (clock_gettime(CLOCK_REALTIME, &ts) != 0) {
    ts.tv_sec = 0;
    ts.tv_nsec = 0;
  }
  ts.tv_sec += 30;
  return ts;
}

static int case_issue8_timespec_get(void) {
  struct timespec ts;
  int base;

  /* The return value is the base that was asked for. */
  base = timespec_get(&ts, CLOCK_REALTIME);
  POSIX_ASSERT_EQ(base, CLOCK_REALTIME);
  POSIX_ASSERT(ts.tv_nsec >= 0 && ts.tv_nsec < 1000000000L);

  /* CLOCK_MONOTONIC works too, and is not required to match REALTIME. */
  base = timespec_get(&ts, CLOCK_MONOTONIC);
  POSIX_ASSERT_EQ(base, CLOCK_MONOTONIC);
  POSIX_ASSERT(ts.tv_nsec >= 0 && ts.tv_nsec < 1000000000L);

  /* An unknown clock is an error, not a silent zero. */
  POSIX_ASSERT_EQ(timespec_get(&ts, 9999), -1);
  POSIX_ASSERT_EQ(errno, EINVAL);

  return POSIX_PASS;
}

static int case_issue8_sem_clockwait_timeout(void) {
  sem_t sem;

  POSIX_ASSERT_EQ(sem_init(&sem, 0, 0), 0);

  /* The semaphore is not available and the deadline has passed: the wait
   * must fail with ETIMEDOUT rather than succeed or block. */
  struct timespec past = past_deadline();
  POSIX_ASSERT_ERRNO(sem_clockwait(&sem, CLOCK_REALTIME, &past), ETIMEDOUT);

  /* A deadline on a different clock works the same way. */
  struct timespec past_mono = past_deadline();
  POSIX_ASSERT_ERRNO(sem_clockwait(&sem, CLOCK_MONOTONIC, &past_mono),
                     ETIMEDOUT);

  /* With the semaphore available the wait succeeds immediately, even with a
   * deadline in the past. */
  POSIX_ASSERT_EQ(sem_post(&sem), 0);
  POSIX_ASSERT_EQ(sem_clockwait(&sem, CLOCK_REALTIME, &past), 0);

  POSIX_ASSERT_EQ(sem_destroy(&sem), 0);
  return POSIX_PASS;
}

static int case_issue8_sem_timedwait_timeout(void) {
  sem_t sem;

  POSIX_ASSERT_EQ(sem_init(&sem, 0, 0), 0);

  /* sem_timedwait() is the CLOCK_REALTIME special case of sem_clockwait(). */
  struct timespec past = past_deadline();
  POSIX_ASSERT_ERRNO(sem_timedwait(&sem, &past), ETIMEDOUT);

  POSIX_ASSERT_EQ(sem_destroy(&sem), 0);
  return POSIX_PASS;
}

/*
 * A mutex that one thread holds until another one releases it.
 *
 * The holder parks on a semaphore rather than on a condition variable: a
 * condition variable would have to be waited on with the mutex held, and
 * pthread_cond_wait() releases the mutex while it waits - which would let
 * the contending thread in and defeat the whole point of the test.
 *
 * Two semaphores are needed, not one. A single one would be a race: the
 * holder's post() and wait() would compete for the same token, and the
 * token meant for the main thread could be taken by the holder itself.
 * `held` carries the "I have the lock" signal, `release` carries the
 * "you may let go" signal.
 */
static pthread_mutex_t held_mutex;
static sem_t mutex_held;
static sem_t mutex_release;

static void *mutex_holder_thread(void *arg) {
  (void)arg;
  if (pthread_mutex_lock(&held_mutex) != 0) {
    return NULL;
  }
  /* Announce that the mutex is taken, then wait for the release. */
  sem_post(&mutex_held);
  sem_wait(&mutex_release);
  pthread_mutex_unlock(&held_mutex);
  return NULL;
}

static int case_issue8_mutex_clocklock_timeout(void) {
  pthread_mutex_t mutex;
  pthread_t holder;
  struct timespec past = past_deadline();
  struct timespec future = future_deadline();

  POSIX_ASSERT_EQ(pthread_mutex_init(&mutex, NULL), 0);

  /* An uncontended mutex locks straight away, whatever the deadline. */
  POSIX_ASSERT_EQ(pthread_mutex_clocklock(&mutex, CLOCK_REALTIME, &future), 0);
  POSIX_ASSERT_EQ(pthread_mutex_unlock(&mutex), 0);

  /*
   * The interesting case needs a second thread to hold the mutex. The
   * holder keeps it until the case releases it, so the timed lock below is
   * guaranteed to contend and has to give up at the deadline.
   */
  POSIX_ASSERT_EQ(pthread_mutex_init(&held_mutex, NULL), 0);
  POSIX_ASSERT_EQ(sem_init(&mutex_held, 0, 0), 0);
  POSIX_ASSERT_EQ(sem_init(&mutex_release, 0, 0), 0);

  POSIX_ASSERT_EQ(pthread_create(&holder, NULL, mutex_holder_thread, NULL), 0);

  /* Wait until the holder actually owns the mutex. */
  sem_wait(&mutex_held);

  /*
   * The deadline has passed, so the lock must not be granted. The pthread
   * interfaces return the error number itself.
   */
  POSIX_ASSERT_EQ(pthread_mutex_clocklock(&held_mutex, CLOCK_REALTIME, &past),
                  ETIMEDOUT);

  /* Release the holder and join it. */
  sem_post(&mutex_release);
  POSIX_ASSERT_EQ(pthread_join(holder, NULL), 0);

  POSIX_ASSERT_EQ(sem_destroy(&mutex_release), 0);
  POSIX_ASSERT_EQ(sem_destroy(&mutex_held), 0);
  POSIX_ASSERT_EQ(pthread_mutex_destroy(&held_mutex), 0);
  POSIX_ASSERT_EQ(pthread_mutex_destroy(&mutex), 0);
  return POSIX_PASS;
}

static int case_issue8_cond_clockwait_timeout(void) {
  pthread_mutex_t mutex;
  pthread_cond_t cond;
  struct timespec past = past_deadline();

  POSIX_ASSERT_EQ(pthread_mutex_init(&mutex, NULL), 0);
  POSIX_ASSERT_EQ(pthread_cond_init(&cond, NULL), 0);

  POSIX_ASSERT_EQ(pthread_mutex_lock(&mutex), 0);

  /*
   * Nobody will ever signal this condition variable, so the wait can only
   * end through the deadline. POSIX says the mutex is owned again on
   * return, whether the wait timed out or not.
   */
  POSIX_ASSERT_EQ(pthread_cond_clockwait(&cond, &mutex, CLOCK_REALTIME, &past),
                  ETIMEDOUT);

  /* The mutex must be owned again. */
  POSIX_ASSERT_EQ(pthread_mutex_unlock(&mutex), 0);

  POSIX_ASSERT_EQ(pthread_cond_destroy(&cond), 0);
  POSIX_ASSERT_EQ(pthread_mutex_destroy(&mutex), 0);
  return POSIX_PASS;
}

/*
 * A read-write lock that one thread holds for writing until another one
 * releases it.
 *
 * As with the mutex above, two semaphores are needed: the holder's post and
 * wait must not compete for the same token.
 */
static pthread_rwlock_t held_rwlock;
static sem_t rwlock_held;
static sem_t rwlock_release;

static void *rw_holder_thread(void *arg) {
  (void)arg;
  if (pthread_rwlock_wrlock(&held_rwlock) != 0) {
    return NULL;
  }
  sem_post(&rwlock_held);
  sem_wait(&rwlock_release);
  pthread_rwlock_unlock(&held_rwlock);
  return NULL;
}

static int case_issue8_rwlock_clock_timeout(void) {
  pthread_rwlock_t rwlock;
  pthread_t holder;
  struct timespec past = past_deadline();
  struct timespec future = future_deadline();

  POSIX_ASSERT_EQ(pthread_rwlock_init(&rwlock, NULL), 0);

  /* Uncontended: the lock is taken immediately. */
  POSIX_ASSERT_EQ(pthread_rwlock_clockrdlock(&rwlock, CLOCK_REALTIME, &future), 0);
  POSIX_ASSERT_EQ(pthread_rwlock_unlock(&rwlock), 0);

  POSIX_ASSERT_EQ(pthread_rwlock_clockwrlock(&rwlock, CLOCK_REALTIME, &future), 0);
  POSIX_ASSERT_EQ(pthread_rwlock_unlock(&rwlock), 0);

  /*
   * The contending case: another thread holds the write lock, so a read
   * lock with a deadline in the past has to give up with ETIMEDOUT
   * instead of waiting for the holder to finish.
   */
  POSIX_ASSERT_EQ(pthread_rwlock_init(&held_rwlock, NULL), 0);
  POSIX_ASSERT_EQ(sem_init(&rwlock_held, 0, 0), 0);
  POSIX_ASSERT_EQ(sem_init(&rwlock_release, 0, 0), 0);

  POSIX_ASSERT_EQ(pthread_create(&holder, NULL, rw_holder_thread, NULL), 0);

  /* Wait until the holder owns the write lock. */
  sem_wait(&rwlock_held);

  POSIX_ASSERT_EQ(pthread_rwlock_clockrdlock(&held_rwlock, CLOCK_REALTIME, &past),
                  ETIMEDOUT);

  /* Release the holder and join it. */
  sem_post(&rwlock_release);
  POSIX_ASSERT_EQ(pthread_join(holder, NULL), 0);

  POSIX_ASSERT_EQ(sem_destroy(&rwlock_release), 0);
  POSIX_ASSERT_EQ(sem_destroy(&rwlock_held), 0);
  POSIX_ASSERT_EQ(pthread_rwlock_destroy(&held_rwlock), 0);
  POSIX_ASSERT_EQ(pthread_rwlock_destroy(&rwlock), 0);
  return POSIX_PASS;
}

/*
 * The clock id is validated before the deadline is ever looked at: an
 * unsupported clock is EINVAL, not ETIMEDOUT. The distinction only shows
 * up on a lock that is actually contended, because an uncontended lock is
 * granted before the deadline matters.
 */
static int case_issue8_clock_id_validation(void) {
  pthread_mutex_t mutex;
  pthread_cond_t cond;
  pthread_rwlock_t rwlock;
  sem_t sem;
  struct timespec past = past_deadline();
  pthread_t holder;

  POSIX_ASSERT_EQ(pthread_mutex_init(&mutex, NULL), 0);
  POSIX_ASSERT_EQ(pthread_cond_init(&cond, NULL), 0);
  POSIX_ASSERT_EQ(pthread_rwlock_init(&rwlock, NULL), 0);
  POSIX_ASSERT_EQ(sem_init(&sem, 0, 0), 0);

  /* An unsupported clock id is rejected outright. */
  POSIX_ASSERT_EQ(pthread_mutex_clocklock(&mutex, 9999, &past), EINVAL);
  POSIX_ASSERT_EQ(pthread_cond_clockwait(&cond, &mutex, 9999, &past), EINVAL);
  POSIX_ASSERT_EQ(pthread_rwlock_clockrdlock(&rwlock, 9999, &past), EINVAL);
  POSIX_ASSERT_EQ(pthread_rwlock_clockwrlock(&rwlock, 9999, &past), EINVAL);
  POSIX_ASSERT_ERRNO(sem_clockwait(&sem, 9999, &past), EINVAL);

  /* A malformed timespec is EINVAL as well. */
  struct timespec bad = {0, 1000000000L};
  POSIX_ASSERT_EQ(pthread_mutex_clocklock(&mutex, CLOCK_REALTIME, &bad), EINVAL);
  POSIX_ASSERT_EQ(pthread_cond_clockwait(&cond, &mutex, CLOCK_REALTIME, &bad),
                  EINVAL);
  POSIX_ASSERT_ERRNO(sem_clockwait(&sem, CLOCK_REALTIME, &bad), EINVAL);

  POSIX_ASSERT_EQ(sem_destroy(&sem), 0);
  POSIX_ASSERT_EQ(pthread_rwlock_destroy(&rwlock), 0);
  POSIX_ASSERT_EQ(pthread_cond_destroy(&cond), 0);
  POSIX_ASSERT_EQ(pthread_mutex_destroy(&mutex), 0);
  (void)holder;
  return POSIX_PASS;
}

/*
 * pthread_condattr_setclock() picks the clock pthread_cond_timedwait()
 * measures its deadline against. The default is CLOCK_REALTIME; a
 * condition variable created with CLOCK_MONOTONIC measures against that
 * instead.
 */
static int case_issue8_condattr_clock(void) {
  pthread_condattr_t attr;
  pthread_cond_t cond;
  pthread_mutex_t mutex;
  clockid_t clock;

  POSIX_ASSERT_EQ(pthread_condattr_init(&attr), 0);

  /* The default is CLOCK_REALTIME. */
  POSIX_ASSERT_EQ(pthread_condattr_getclock(&attr, &clock), 0);
  POSIX_ASSERT_EQ(clock, CLOCK_REALTIME);

  /* An unsupported clock is rejected. */
  POSIX_ASSERT_EQ(pthread_condattr_setclock(&attr, 9999), EINVAL);

  /* A supported one is accepted. */
  POSIX_ASSERT_EQ(pthread_condattr_setclock(&attr, CLOCK_MONOTONIC), 0);
  POSIX_ASSERT_EQ(pthread_condattr_getclock(&attr, &clock), 0);
  POSIX_ASSERT_EQ(clock, CLOCK_MONOTONIC);

  /*
   * The condition variable inherits the clock at creation time, and
   * pthread_cond_timedwait() then measures its deadline against it.
   */
  POSIX_ASSERT_EQ(pthread_cond_init(&cond, &attr), 0);
  POSIX_ASSERT_EQ(pthread_mutex_init(&mutex, NULL), 0);
  POSIX_ASSERT_EQ(pthread_mutex_lock(&mutex), 0);

  struct timespec past = past_deadline();
  POSIX_ASSERT_EQ(pthread_cond_timedwait(&cond, &mutex, &past), ETIMEDOUT);
  POSIX_ASSERT_EQ(pthread_mutex_unlock(&mutex), 0);

  /* A condition variable without an attribute defaults to CLOCK_REALTIME. */
  pthread_cond_t plain;
  POSIX_ASSERT_EQ(pthread_cond_init(&plain, NULL), 0);
  POSIX_ASSERT_EQ(pthread_mutex_lock(&mutex), 0);
  POSIX_ASSERT_EQ(pthread_cond_timedwait(&plain, &mutex, &past), ETIMEDOUT);
  POSIX_ASSERT_EQ(pthread_mutex_unlock(&mutex), 0);

  POSIX_ASSERT_EQ(pthread_cond_destroy(&plain), 0);
  POSIX_ASSERT_EQ(pthread_cond_destroy(&cond), 0);
  POSIX_ASSERT_EQ(pthread_mutex_destroy(&mutex), 0);
  POSIX_ASSERT_EQ(pthread_condattr_destroy(&attr), 0);
  return POSIX_PASS;
}

/*
 * pthread_rwlock_tryrdlock() and pthread_rwlock_trywrlock() report a
 * failure as EBUSY. Handing out the lock's internal state word instead
 * would be a number POSIX never defined, and one whose meaning changes
 * between calls.
 */
static int case_issue8_rwlock_try_busy(void) {
  pthread_rwlock_t rwlock;

  POSIX_ASSERT_EQ(pthread_rwlock_init(&rwlock, NULL), 0);

  /* Uncontended: both try variants succeed. */
  POSIX_ASSERT_EQ(pthread_rwlock_tryrdlock(&rwlock), 0);
  POSIX_ASSERT_EQ(pthread_rwlock_unlock(&rwlock), 0);
  POSIX_ASSERT_EQ(pthread_rwlock_trywrlock(&rwlock), 0);
  POSIX_ASSERT_EQ(pthread_rwlock_unlock(&rwlock), 0);

  /* While the write lock is held, both try variants report EBUSY. */
  POSIX_ASSERT_EQ(pthread_rwlock_wrlock(&rwlock), 0);
  POSIX_ASSERT_EQ(pthread_rwlock_trywrlock(&rwlock), EBUSY);
  POSIX_ASSERT_EQ(pthread_rwlock_tryrdlock(&rwlock), EBUSY);
  POSIX_ASSERT_EQ(pthread_rwlock_unlock(&rwlock), 0);

  /* The same holds while a read lock is held. */
  POSIX_ASSERT_EQ(pthread_rwlock_rdlock(&rwlock), 0);
  POSIX_ASSERT_EQ(pthread_rwlock_trywrlock(&rwlock), EBUSY);
  POSIX_ASSERT_EQ(pthread_rwlock_unlock(&rwlock), 0);

  POSIX_ASSERT_EQ(pthread_rwlock_destroy(&rwlock), 0);
  return POSIX_PASS;
}

/*
 * The opaque synchronization objects have to be exactly as large as the
 * kernel's objects.
 *
 * The kernel writes its own object into the caller's storage, so a C type
 * that is too small means the kernel writes past the end of it. That is
 * silent memory corruption, and it does not necessarily show up as a crash:
 * the neighbouring stack slot is simply clobbered.
 *
 * The Rust side asserts its own sizes, and the C headers assert theirs, but
 * neither can see the other side. This case is what ties the two together:
 * it fails the moment one of them moves and the other does not.
 */
static int case_issue8_sync_object_sizes(void) {
  /* The condition variable carries the clock its deadlines are measured
   * on, so it is larger than the two counters it started out as. */
  POSIX_ASSERT_EQ(sizeof(pthread_cond_t), 24);
  POSIX_ASSERT_EQ(_Alignof(pthread_cond_t), 8);

  POSIX_ASSERT_EQ(sizeof(pthread_mutex_t), 24);
  POSIX_ASSERT_EQ(_Alignof(pthread_mutex_t), 8);

  POSIX_ASSERT_EQ(sizeof(pthread_rwlock_t), 8);
  POSIX_ASSERT_EQ(_Alignof(pthread_rwlock_t), 8);

  POSIX_ASSERT_EQ(sizeof(pthread_barrier_t), 48);
  POSIX_ASSERT_EQ(_Alignof(pthread_barrier_t), 8);

  /* The C11 types have their own storage for the same reason. */
  POSIX_ASSERT_EQ(sizeof(cnd_t), 24);
  POSIX_ASSERT_EQ(_Alignof(cnd_t), 8);
  POSIX_ASSERT_EQ(sizeof(mtx_t), 24);
  POSIX_ASSERT_EQ(_Alignof(mtx_t), 8);

  return POSIX_PASS;
}

POSIX_CASE("issue8_timespec_get", case_issue8_timespec_get);
POSIX_CASE("issue8_sem_clockwait_timeout", case_issue8_sem_clockwait_timeout);
POSIX_CASE("issue8_sem_timedwait_timeout", case_issue8_sem_timedwait_timeout);
POSIX_CASE("issue8_mutex_clocklock_timeout", case_issue8_mutex_clocklock_timeout);
POSIX_CASE("issue8_cond_clockwait_timeout", case_issue8_cond_clockwait_timeout);
POSIX_CASE("issue8_rwlock_clock_timeout", case_issue8_rwlock_clock_timeout);
POSIX_CASE("issue8_clock_id_validation", case_issue8_clock_id_validation);
POSIX_CASE("issue8_condattr_clock", case_issue8_condattr_clock);
POSIX_CASE("issue8_rwlock_try_busy", case_issue8_rwlock_try_busy);
POSIX_CASE("issue8_sync_object_sizes", case_issue8_sync_object_sizes);
