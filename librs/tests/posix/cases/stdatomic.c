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
 * <stdatomic.h> - all 27 Issue 8 interfaces.
 *
 * clang ships this header, and on aarch64/rv64 every operation lowers to a
 * native instruction, so there is nothing to implement. What is worth
 * checking is the other half: that the operations still behave like atomics
 * once they are running. A header that compiles but silently lowers an
 * atomic_fetch_add to a plain load/add/store passes every compile-only test
 * and breaks the first real user, so this case checks results and, at the
 * end, checks atomicity under four concurrent threads.
 */

#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>

#include "posix_case.h"

static int case_c11_atomic_operations(void) {
  atomic_int a;
  atomic_flag flag = ATOMIC_FLAG_INIT;
  int expected;
  int old;

  /* atomic_init + atomic_load */
  atomic_init(&a, 5);
  POSIX_ASSERT_EQ(atomic_load(&a), 5);
  POSIX_ASSERT_EQ(atomic_load_explicit(&a, memory_order_acquire), 5);

  /* A plain int is lock free on both boards. A 0 here would mean every
   * operation below is going through a hidden lock. */
  POSIX_ASSERT_EQ(atomic_is_lock_free(&a), 1);

  /* atomic_store */
  atomic_store(&a, 10);
  POSIX_ASSERT_EQ(atomic_load(&a), 10);
  atomic_store_explicit(&a, 11, memory_order_relaxed);
  POSIX_ASSERT_EQ(atomic_load(&a), 11);

  /* atomic_exchange returns the previous value. */
  old = atomic_exchange(&a, 20);
  POSIX_ASSERT_EQ(old, 11);
  POSIX_ASSERT_EQ(atomic_load(&a), 20);
  old = atomic_exchange_explicit(&a, 21, memory_order_acq_rel);
  POSIX_ASSERT_EQ(old, 20);

  /* atomic_compare_exchange_strong: matching expectation swaps. */
  expected = 21;
  POSIX_ASSERT_EQ(atomic_compare_exchange_strong(&a, &expected, 30), 1);
  POSIX_ASSERT_EQ(atomic_load(&a), 30);
  /* Non-matching expectation leaves the value alone and reports failure,
   * and writes the value it actually saw back into `expected`. */
  expected = 999;
  POSIX_ASSERT_EQ(atomic_compare_exchange_strong(&a, &expected, 40), 0);
  POSIX_ASSERT_EQ(atomic_load(&a), 30);
  POSIX_ASSERT_EQ(expected, 30);

  expected = 30;
  POSIX_ASSERT_EQ(
      atomic_compare_exchange_strong_explicit(&a, &expected, 31,
                                              memory_order_acq_rel,
                                              memory_order_acquire),
      1);
  POSIX_ASSERT_EQ(atomic_load(&a), 31);

  /* atomic_compare_exchange_weak may fail spuriously, so retry it. A
   * correct implementation converges; a broken one spins forever, which the
   * harness timeout turns into a failure instead of a hang. */
  expected = 31;
  while (!atomic_compare_exchange_weak(&a, &expected, 32)) {
    expected = 31;
  }
  POSIX_ASSERT_EQ(atomic_load(&a), 32);

  expected = 32;
  while (!atomic_compare_exchange_weak_explicit(&a, &expected, 33,
                                                memory_order_acq_rel,
                                                memory_order_acquire)) {
    expected = 32;
  }
  POSIX_ASSERT_EQ(atomic_load(&a), 33);

  /* fetch_* return the value before the operation. */
  POSIX_ASSERT_EQ(atomic_fetch_add(&a, 7), 33);
  POSIX_ASSERT_EQ(atomic_load(&a), 40);
  POSIX_ASSERT_EQ(atomic_fetch_add_explicit(&a, 2, memory_order_relaxed), 40);

  POSIX_ASSERT_EQ(atomic_fetch_sub(&a, 10), 42);
  POSIX_ASSERT_EQ(atomic_load(&a), 32);
  POSIX_ASSERT_EQ(atomic_fetch_sub_explicit(&a, 2, memory_order_relaxed), 32);

  POSIX_ASSERT_EQ(atomic_fetch_or(&a, 0xf0), 30);
  POSIX_ASSERT_EQ(atomic_load(&a), 0xfe);
  POSIX_ASSERT_EQ(atomic_fetch_or_explicit(&a, 0, memory_order_relaxed), 0xfe);

  POSIX_ASSERT_EQ(atomic_fetch_xor(&a, 0x0f), 0xfe);
  POSIX_ASSERT_EQ(atomic_load(&a), 0xf1);
  POSIX_ASSERT_EQ(atomic_fetch_xor_explicit(&a, 0, memory_order_relaxed), 0xf1);

  POSIX_ASSERT_EQ(atomic_fetch_and(&a, 0x0f), 0xf1);
  POSIX_ASSERT_EQ(atomic_load(&a), 0x01);
  POSIX_ASSERT_EQ(atomic_fetch_and_explicit(&a, 0xff, memory_order_relaxed),
                  0x01);

  /* atomic_flag: the first test-and-set acquires it, the second sees it
   * already set. */
  POSIX_ASSERT_EQ(atomic_flag_test_and_set(&flag), 0);
  POSIX_ASSERT_EQ(atomic_flag_test_and_set(&flag), 1);
  atomic_flag_clear(&flag);
  POSIX_ASSERT_EQ(atomic_flag_test_and_set_explicit(&flag,
                                                    memory_order_acquire),
                  0);
  atomic_flag_clear_explicit(&flag, memory_order_release);

  /* Fences are no-ops for a single thread; they are listed because Issue 8
   * requires them and a missing one is a compile error, not a runtime one. */
  atomic_thread_fence(memory_order_seq_cst);
  atomic_signal_fence(memory_order_seq_cst);

  return POSIX_PASS;
}

/*
 * The concurrency half. Four threads each add 5000 to a shared counter; a
 * non-atomic increment loses updates, so the total is the assertion that
 * separates "atomic" from "compiles".
 */
#define SHARED_THREADS 4
#define SHARED_ADDS 5000

static atomic_int shared_counter;
static atomic_int shared_ready;

static void *adder(void *arg) {
  int i;
  (void)arg;
  for (i = 0; i < SHARED_ADDS; i++) {
    atomic_fetch_add(&shared_counter, 1);
  }
  atomic_fetch_add(&shared_ready, 1);
  return NULL;
}

static int case_c11_atomic_is_atomic(void) {
  pthread_t threads[SHARED_THREADS];
  int i;

  atomic_init(&shared_counter, 0);
  atomic_init(&shared_ready, 0);

  for (i = 0; i < SHARED_THREADS; i++) {
    POSIX_ASSERT_EQ(pthread_create(&threads[i], NULL, adder, NULL), 0);
  }
  for (i = 0; i < SHARED_THREADS; i++) {
    POSIX_ASSERT_EQ(pthread_join(threads[i], NULL), 0);
  }

  POSIX_ASSERT_EQ(atomic_load(&shared_ready), SHARED_THREADS);
  POSIX_ASSERT_EQ(atomic_load(&shared_counter), SHARED_THREADS * SHARED_ADDS);
  return POSIX_PASS;
}

POSIX_CASE("stdatomic_operations", case_c11_atomic_operations);
POSIX_CASE("stdatomic_is_atomic", case_c11_atomic_is_atomic);
