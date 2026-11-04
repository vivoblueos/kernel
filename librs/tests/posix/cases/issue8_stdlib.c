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
 * The Issue 8 allocator and wide-string interfaces newlib already ships.
 *
 * quick_exit() is deliberately not exercised: it terminates the process, and
 * every case here runs inside one process shared with the runner. Calling it
 * would end the whole run after it, which looks like a pass in the log and is
 * actually a silent truncation of the suite. at_quick_exit() is checked for
 * registration only, and the gap is recorded rather than papered over.
 */

#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

#include "posix_case.h"

static int case_issue8_aligned_alloc(void) {
  size_t alignment = 64;
  size_t size = 256; /* Issue 8: size must be a multiple of alignment. */
  void *p;

  p = aligned_alloc(alignment, size);
  POSIX_ASSERT(p != NULL);
  POSIX_ASSERT_EQ(((uintptr_t)p % alignment), 0);

  /* The whole block has to be writable - a pointer that is aligned but
   * backed by nothing fails here rather than in the caller. */
  memset(p, 0x5a, size);
  POSIX_ASSERT_EQ(((unsigned char *)p)[size - 1], 0x5a);
  free(p);

  /*
   * A non-power-of-two alignment is rejected. The value goes through a
   * volatile variable because clang folds a literal 3 into the builtin and
   * turns the call into -Wnon-power-of-two-alignment, which is -Werror here
   * - a diagnostic about the test's own source, not about aligned_alloc.
   */
  volatile size_t bad_alignment = 3;
  errno = 0;
  POSIX_ASSERT(aligned_alloc(bad_alignment, 9) == NULL);
  POSIX_ASSERT_EQ(errno, EINVAL);

  return POSIX_PASS;
}

static int case_issue8_reallocarray(void) {
  int *nums;
  size_t i;

  nums = (int *)reallocarray(NULL, 8, sizeof(int));
  POSIX_ASSERT(nums != NULL);
  for (i = 0; i < 8; i++) {
    nums[i] = (int)i;
  }

  /* Growing keeps the old contents. */
  nums = (int *)reallocarray(nums, 32, sizeof(int));
  POSIX_ASSERT(nums != NULL);
  for (i = 0; i < 8; i++) {
    POSIX_ASSERT_EQ(nums[i], (int)i);
  }
  free(nums);

  /*
   * The point of reallocarray over realloc: a multiplication that overflows
   * is a failure, not a small allocation the caller then overruns.
   *
   * The factor goes through a volatile variable because gcc folds the literal
   * and rejects the call with -Walloc-size-larger-than (an error under
   * -Werror), which is a complaint about this source file rather than about
   * reallocarray. The overflow has to reach the function at run time to be
   * tested at all.
   */
  volatile size_t too_many = SIZE_MAX;
  errno = 0;
  POSIX_ASSERT(reallocarray(NULL, too_many, 2) == NULL);
  POSIX_ASSERT_EQ(errno, ENOMEM);

  return POSIX_PASS;
}

static int case_issue8_wcslcpy_wcslcat(void) {
  wchar_t buf[8];
  size_t wanted;

  POSIX_ASSERT_EQ(wcslcpy(buf, L"abc", 8), 3);
  POSIX_ASSERT_EQ(wcscmp(buf, L"abc"), 0);

  /* Same contract as strlcpy: the return value is what it wanted to write. */
  wanted = wcslcpy(buf, L"abcdefghij", 8);
  POSIX_ASSERT_EQ(wanted, 10);
  POSIX_ASSERT_EQ(wcscmp(buf, L"abcdefg"), 0);

  POSIX_ASSERT_EQ(wcslcpy(buf, L"ab", 8), 2);
  POSIX_ASSERT_EQ(wcslcat(buf, L"cd", 8), 4);
  POSIX_ASSERT_EQ(wcscmp(buf, L"abcd"), 0);

  POSIX_ASSERT_EQ(wcslcpy(buf, L"ab", 8), 2);
  wanted = wcslcat(buf, L"cdefghij", 8);
  POSIX_ASSERT_EQ(wanted, 10);
  POSIX_ASSERT_EQ(wcscmp(buf, L"abcdefg"), 0);

  return POSIX_PASS;
}

/*
 * newlib defines qsort_r in two flavours and picks one with feature macros:
 * the GNU one takes the thunk last, the BSD one takes it before the
 * comparator and passes it as the comparator's first argument.
 *
 * Which one you get depends on _GNU_SOURCE, and the build turns it on for
 * the whole image, so this is the GNU shape: thunk last, comparator takes it
 * as its third argument. Getting this backwards is not harmless - the
 * comparator receives the thunk in place of a value pointer and dereferences
 * it, so the callback below records the thunk it actually received and the
 * case asserts on it. Checking only the sorted order would pass either way
 * if the array happened to sort correctly by luck.
 */
static void *g_seen_thunk;

static int compare_with_thunk(const void *a, const void *b, void *thunk) {
  g_seen_thunk = thunk;
  return *(const int *)a - *(const int *)b;
}

static int case_issue8_qsort_r(void) {
  int values[] = {5, 3, 1, 4, 2};
  int marker = 42;

  g_seen_thunk = NULL;
  qsort_r(values, 5, sizeof(int), compare_with_thunk, &marker);

  POSIX_ASSERT_EQ(values[0], 1);
  POSIX_ASSERT_EQ(values[1], 2);
  POSIX_ASSERT_EQ(values[2], 3);
  POSIX_ASSERT_EQ(values[3], 4);
  POSIX_ASSERT_EQ(values[4], 5);

  /* If this is NULL the comparator was called with the wrong argument in
   * the thunk slot - i.e. the other qsort_r flavour got linked. */
  POSIX_ASSERT(g_seen_thunk == &marker);

  return POSIX_PASS;
}

static void quick_exit_handler(void) {}

static int case_issue8_at_quick_exit(void) {
  POSIX_ASSERT_EQ(at_quick_exit(quick_exit_handler), 0);
  return POSIX_PASS;
}

POSIX_CASE("issue8_aligned_alloc", case_issue8_aligned_alloc);
POSIX_CASE("issue8_reallocarray", case_issue8_reallocarray);
POSIX_CASE("issue8_wcslcpy_wcslcat", case_issue8_wcslcpy_wcslcat);
POSIX_CASE("issue8_qsort_r", case_issue8_qsort_r);
POSIX_CASE("issue8_at_quick_exit", case_issue8_at_quick_exit);
