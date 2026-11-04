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

#ifndef LIBRS_TESTS_POSIX_CASE_H
#define LIBRS_TESTS_POSIX_CASE_H

#include <errno.h>
#include <stddef.h>

/* Return codes understood by runner.c. */
#define POSIX_PASS 0
#define POSIX_FAIL 1
#define POSIX_SKIP 77

struct posix_case {
  const char *name;
  int (*run)(void);
  /*
   * NULL for a case that must pass. Otherwise a one-line reason why the case
   * is expected to fail today; the runner then reports it as a known defect
   * instead of a regression.
   */
  const char *known_issue;
};

/*
 * Each case registers itself in its own section. The linker script keeps the
 * section and provides __start_posix_cases/__stop_posix_cases, so adding a
 * file to the build is enough to add a case to the run - no central list.
 */
#define POSIX_CASE(case_name, case_fn)                                       \
  static const struct posix_case __posix_case_##case_fn                      \
      __attribute__((used, section(".posix_cases"))) = {                     \
          case_name,                                                         \
          case_fn,                                                           \
          NULL,                                                              \
  }

/*
 * Registers a case that reproduces a defect that is known but not yet fixed.
 * The runner reports it as POSIX-KNOWN-FAIL and, crucially, fails the run with
 * POSIX-XPASS if it ever starts passing - a known defect that stops
 * reproducing is a stale marker, and leaving it in the tree would silently
 * hide the next regression in the same call path.
 *
 * `reason` must name the defect, not restate the assertion.
 */
#define POSIX_CASE_XFAIL(case_name, case_fn, reason)                         \
  static const struct posix_case __posix_case_##case_fn                      \
      __attribute__((used, section(".posix_cases"))) = {                     \
          case_name,                                                         \
          case_fn,                                                           \
          reason,                                                            \
  }

void posix_say(const char *text);
void posix_sayf(const char *prefix, long value);

#define POSIX_ASSERT(cond)                                                   \
  do {                                                                       \
    if (!(cond)) {                                                           \
      posix_say("  assertion failed: " #cond);                               \
      return POSIX_FAIL;                                                     \
    }                                                                        \
  } while (0)

#define POSIX_ASSERT_EQ(actual, expected)                                    \
  do {                                                                       \
    long __actual = (long)(actual);                                          \
    long __expected = (long)(expected);                                      \
    if (__actual != __expected) {                                            \
      posix_sayf("  expected ", __expected);                                 \
      posix_sayf("  actual   ", __actual);                                   \
      posix_say("  assertion failed: " #actual " == " #expected);            \
      return POSIX_FAIL;                                                     \
    }                                                                        \
  } while (0)

/*
 * Checks both halves of the POSIX failure contract: the call returns -1 and
 * errno carries the expected code. A call that fails with the wrong errno is a
 * different bug from a call that succeeds.
 */
#define POSIX_ASSERT_ERRNO(expr, expected)                                   \
  do {                                                                       \
    errno = 0;                                                               \
    long __result = (long)(expr);                                            \
    int __expected = (expected);                                             \
    if (__result != -1 || errno != __expected) {                             \
      posix_sayf("  expected errno ", __expected);                           \
      posix_sayf("  actual errno   ", errno);                                \
      posix_say("  assertion failed: " #expr " fails with errno");           \
      return POSIX_FAIL;                                                     \
    }                                                                        \
  } while (0)

#endif /* LIBRS_TESTS_POSIX_CASE_H */
