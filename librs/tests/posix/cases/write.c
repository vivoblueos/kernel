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

#include <fcntl.h>
#include <string.h>
#include <unistd.h>

#include "posix_case.h"

/* Root tmpfs; see open.c for why not /tmp. */
#define POSIX_WRITE_PATH "/posix-write.txt"

static int run(void) {
  static const char payload[] = "posix-write";
  const size_t length = sizeof(payload) - 1;
  char readback[sizeof(payload)];

  int fd = open(POSIX_WRITE_PATH, O_CREAT | O_RDWR | O_TRUNC, 0666);
  POSIX_ASSERT(fd >= 0);
  POSIX_ASSERT_EQ(write(fd, payload, length), (long)length);
  POSIX_ASSERT_EQ(close(fd), 0);

  memset(readback, 0, sizeof(readback));
  fd = open(POSIX_WRITE_PATH, O_RDONLY);
  POSIX_ASSERT(fd >= 0);
  POSIX_ASSERT_EQ(read(fd, readback, length), (long)length);
  POSIX_ASSERT_EQ(close(fd), 0);
  POSIX_ASSERT(memcmp(readback, payload, length) == 0);

  return POSIX_PASS;
}

POSIX_CASE("write", run);
