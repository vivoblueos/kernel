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
 * The Issue 8 string and signal-name interfaces that newlib already ships.
 *
 * These need no implementation work, which is exactly why they are worth a
 * case: "the symbol resolved at link time" is not the same claim as "the
 * function does what Issue 8 says". strlcpy in particular is easy to get
 * wrong at the boundary - it must return the length it *wanted* to write,
 * not the length it did write, and that difference is invisible unless the
 * destination is too small.
 */

#include <signal.h>
#include <string.h>

#include "posix_case.h"

static int case_issue8_memmem(void) {
  const char haystack[] = "the quick brown fox";
  char *hit;

  /* Present, and pointing at the right offset. */
  hit = (char *)memmem(haystack, sizeof(haystack) - 1, "brown", 5);
  POSIX_ASSERT(hit != NULL);
  POSIX_ASSERT_EQ(hit - haystack, 10);

  /* Absent. */
  POSIX_ASSERT(memmem(haystack, sizeof(haystack) - 1, "cat", 3) == NULL);

  /* A zero-length needle is found at offset 0, per Issue 8. */
  hit = (char *)memmem(haystack, sizeof(haystack) - 1, "", 0);
  POSIX_ASSERT(hit != NULL);
  POSIX_ASSERT_EQ(hit - haystack, 0);

  /* A needle longer than the haystack cannot match. */
  POSIX_ASSERT(memmem(haystack, 3, "the quick brown fox", 19) == NULL);

  return POSIX_PASS;
}

static int case_issue8_strlcpy_strlcat(void) {
  char buf[8];
  size_t wanted;

  /* Fits: returns the source length, and the result is terminated. */
  memset(buf, 0xaa, sizeof(buf));
  POSIX_ASSERT_EQ(strlcpy(buf, "abc", sizeof(buf)), 3);
  POSIX_ASSERT_EQ(strcmp(buf, "abc"), 0);

  /* Does not fit: returns the length it wanted, writes size-1 bytes plus a
   * terminator, and does not run past the buffer. */
  memset(buf, 0xaa, sizeof(buf));
  wanted = strlcpy(buf, "abcdefghij", sizeof(buf));
  POSIX_ASSERT_EQ(wanted, 10);
  POSIX_ASSERT_EQ(strcmp(buf, "abcdefg"), 0);

  /* strlcat appends and, like strlcpy, reports the length it wanted, which
   * is the length of the result it would have produced. */
  memset(buf, 0xaa, sizeof(buf));
  POSIX_ASSERT_EQ(strlcpy(buf, "ab", sizeof(buf)), 2);
  POSIX_ASSERT_EQ(strlcat(buf, "cd", sizeof(buf)), 4);
  POSIX_ASSERT_EQ(strcmp(buf, "abcd"), 0);

  /* Truncating append. */
  memset(buf, 0xaa, sizeof(buf));
  POSIX_ASSERT_EQ(strlcpy(buf, "ab", sizeof(buf)), 2);
  wanted = strlcat(buf, "cdefghij", sizeof(buf));
  POSIX_ASSERT_EQ(wanted, 10);
  POSIX_ASSERT_EQ(strcmp(buf, "abcdefg"), 0);

  return POSIX_PASS;
}

static int case_issue8_sig2str_str2sig(void) {
  char name[32];
  int signo;

  /* Round trip through the name space. Issue 8 names signals without the
   * "SIG" prefix, so "HUP" - not "SIGHUP" - is what has to come back. */
  POSIX_ASSERT_EQ(sig2str(SIGHUP, name), 0);
  POSIX_ASSERT_EQ(strcmp(name, "HUP"), 0);
  POSIX_ASSERT_EQ(str2sig(name, &signo), 0);
  POSIX_ASSERT_EQ(signo, SIGHUP);

  POSIX_ASSERT_EQ(sig2str(SIGTERM, name), 0);
  POSIX_ASSERT_EQ(strcmp(name, "TERM"), 0);
  POSIX_ASSERT_EQ(str2sig("TERM", &signo), 0);
  POSIX_ASSERT_EQ(signo, SIGTERM);

  /* An unknown name is a failure, and it must not leave the output
   * untouched-as-success behind. */
  signo = 12345;
  POSIX_ASSERT_EQ(str2sig("NO SUCH SIGNAL", &signo), -1);

  /* A signal number with no name is likewise a failure. */
  POSIX_ASSERT_EQ(sig2str(-1, name), -1);

  return POSIX_PASS;
}

POSIX_CASE("issue8_memmem", case_issue8_memmem);
POSIX_CASE("issue8_strlcpy_strlcat", case_issue8_strlcpy_strlcat);
POSIX_CASE("issue8_sig2str_str2sig", case_issue8_sig2str_str2sig);
