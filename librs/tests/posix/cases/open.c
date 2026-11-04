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
#include <fcntl.h>
#include <unistd.h>

#include "posix_case.h"

/*
 * Paths live in the root tmpfs. /tmp is not mounted by default on this board
 * (vfs_init mounts /dev, /fat and /proc only), so a case that assumed it would
 * fail on the mount table rather than on open().
 */
#define POSIX_OPEN_PATH "/posix-open.txt"
#define POSIX_OPEN_MISSING "/posix-open-missing.txt"

static int run(void) {
  int fd;

  /* Create, then reopen read-only: two distinct open paths (with and without
   * O_CREAT, which is where the variadic mode argument is read). */
  fd = open(POSIX_OPEN_PATH, O_CREAT | O_RDWR | O_TRUNC, 0600);
  POSIX_ASSERT(fd >= 0);
  POSIX_ASSERT_EQ(close(fd), 0);

  fd = open(POSIX_OPEN_PATH, O_RDONLY);
  POSIX_ASSERT(fd >= 0);
  POSIX_ASSERT_EQ(close(fd), 0);

  /* POSIX failure contract: -1 and a meaningful errno, not just "negative". */
  POSIX_ASSERT_ERRNO(open(POSIX_OPEN_MISSING, O_RDONLY), ENOENT);

  return POSIX_PASS;
}

POSIX_CASE("open", run);
