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

#include <errno.h>
#include <time.h>
#include <unistd.h>

#include "posix_case.h"

#define POSIX_NS_PER_SEC 1000000000L

static int valid(const struct timespec *ts) {
  return ts->tv_sec >= 0 && ts->tv_nsec >= 0 && ts->tv_nsec < POSIX_NS_PER_SEC;
}

static int later(const struct timespec *after, const struct timespec *before) {
  if (after->tv_sec != before->tv_sec) {
    return after->tv_sec > before->tv_sec;
  }
  return after->tv_nsec > before->tv_nsec;
}

/*
 * The interesting part of this case is the clock id, not the clock. newlib
 * numbers CLOCK_REALTIME 1 and CLOCK_MONOTONIC 4 while the kernel uses 0 and 1,
 * so an untranslated id makes the two clocks swap: reading CLOCK_REALTIME
 * returns the monotonic clock (tv_sec == 0, and a negative tv_nsec before the
 * first tick lands) and reading CLOCK_MONOTONIC fails with EINVAL.
 */
static int run(void) {
  struct timespec realtime;
  struct timespec monotonic_before;
  struct timespec monotonic_after;
  struct timespec resolution;

  monotonic_before.tv_sec = -1;
  monotonic_before.tv_nsec = -1;
  realtime.tv_sec = -1;
  realtime.tv_nsec = -1;

  errno = 0;
  posix_sayf("  rc(mono) ", clock_gettime(CLOCK_MONOTONIC, &monotonic_before));
  posix_sayf("  errno(mono) ", errno);
  posix_sayf("  mono.sec ", (long)monotonic_before.tv_sec);
  posix_sayf("  mono.nsec ", (long)monotonic_before.tv_nsec);

  errno = 0;
  posix_sayf("  rc(real) ", clock_gettime(CLOCK_REALTIME, &realtime));
  posix_sayf("  errno(real) ", errno);
  posix_sayf("  real.sec ", (long)realtime.tv_sec);
  posix_sayf("  real.nsec ", (long)realtime.tv_nsec);
  posix_sayf("  time(NULL) ", (long)time(NULL));
  posix_sayf("  clock() ", (long)clock());

  POSIX_ASSERT_EQ(clock_gettime(CLOCK_REALTIME, &realtime), 0);
  if (!valid(&realtime)) {
    posix_sayf("  realtime.tv_sec  ", (long)realtime.tv_sec);
    posix_sayf("  realtime.tv_nsec ", (long)realtime.tv_nsec);
  }
  POSIX_ASSERT(valid(&realtime));

  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &monotonic_before), 0);
  POSIX_ASSERT(valid(&monotonic_before));

  POSIX_ASSERT_EQ(clock_getres(CLOCK_MONOTONIC, &resolution), 0);
  POSIX_ASSERT(valid(&resolution));

  {
    /* nanosleep rather than usleep: newlib's <unistd.h> does not declare
     * usleep under _POSIX_C_SOURCE=200809L (POSIX dropped it in 2008). */
    struct timespec pause = {0, 20000000L};
    POSIX_ASSERT_EQ(nanosleep(&pause, NULL), 0);
  }

  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &monotonic_after), 0);
  POSIX_ASSERT(later(&monotonic_after, &monotonic_before));

  /* POSIX requires EINVAL for a clock the implementation does not provide. */
  POSIX_ASSERT_ERRNO(clock_gettime((clockid_t)0x7fff, &realtime), EINVAL);

  return POSIX_PASS;
}

POSIX_CASE("clock_gettime", run);
