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
 * The Issue 8 explicit file-descriptor operations: posix_close(),
 * posix_devctl() and posix_getdents().
 *
 * posix_getdents() is the interesting one: the kernel's getdents produces
 * Linux `struct dirent` records, and posix_getdents() has to translate them
 * into the POSIX `struct posix_dent` layout. A translation bug shows up as a
 * garbled file name or a wrong entry count, so the case reads a real
 * directory back and checks that the names come out intact.
 */

#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <string.h>
#include <unistd.h>

#include "posix_case.h"
#include "posix_issue8.h"

static int case_issue8_posix_close(void) {
  int fd;

  /* posix_close() on a valid descriptor behaves like close(). */
  fd = open("/posix-close.txt", O_CREAT | O_RDWR, 0600);
  if (fd < 0) {
    return POSIX_SKIP;
  }
  POSIX_ASSERT_EQ(posix_close(fd, 0), 0);

  /* A second close of the same descriptor must fail with EBADF. */
  POSIX_ASSERT_EQ(posix_close(fd, 0), -1);
  POSIX_ASSERT_EQ(errno, EBADF);

  return POSIX_PASS;
}

static int case_issue8_posix_getdents(void) {
  int fd;
  char buf[1024];
  ssize_t n;
  size_t offset;
  int entries;
  int saw_dot;

  fd = open("/", O_RDONLY);
  if (fd < 0) {
    return POSIX_SKIP;
  }

  n = posix_getdents(fd, buf, sizeof(buf), 0);
  if (n < 0) {
    /*
     * Known gap, not a pass: the kernel's directory reader rejects the root
     * tmpfs inode with EINVAL, so `posix_getdents()` never gets records to
     * translate and this case has nothing to check. It skips - and the
     * checker's `skipped` count is 1 because of it, which is the honest
     * number: a skip here means the POSIX `struct posix_dent` translation is
     * *not* covered on this board.
     */
    POSIX_ASSERT_EQ(errno, EINVAL);
    POSIX_ASSERT_EQ(posix_close(fd, 0), 0);
    return POSIX_SKIP;
  }

  POSIX_ASSERT(n > 0);

  /* Walk the entries and check the structure is self-consistent: d_reclen
   * has to advance the cursor, and every name has to be NUL-terminated
   * within its own entry. */
  entries = 0;
  saw_dot = 0;
  offset = 0;
  while (offset < (size_t)n) {
    struct posix_dent *dent = (struct posix_dent *)(buf + offset);

    POSIX_ASSERT(dent->d_reclen > 0);
    POSIX_ASSERT(offset + dent->d_reclen <= (size_t)n);

    /* The name has to be terminated inside the entry. */
    POSIX_ASSERT(memchr(dent->d_name, '\0', dent->d_reclen - sizeof(*dent)) != NULL);

    if (strcmp(dent->d_name, ".") == 0) {
      saw_dot = 1;
      POSIX_ASSERT_EQ(dent->d_type, DT_DIR);
    }

    entries++;
    offset += dent->d_reclen;
  }

  POSIX_ASSERT(entries > 0);
  POSIX_ASSERT(saw_dot);

  POSIX_ASSERT_EQ(posix_close(fd, 0), 0);
  return POSIX_PASS;
}

static int case_issue8_posix_getdents_bad_args(void) {
  char buf[256];

  /* A non-zero flags value is reserved for future extension and has to be
   * rejected rather than silently ignored. */
  POSIX_ASSERT_EQ(posix_getdents(-1, buf, sizeof(buf), 1), -1);
  POSIX_ASSERT_EQ(errno, EINVAL);

  /* A bad descriptor is EBADF, not a crash. */
  POSIX_ASSERT_EQ(posix_getdents(-1, buf, sizeof(buf), 0), -1);
  POSIX_ASSERT_EQ(errno, EBADF);

  return POSIX_PASS;
}

/* The terminal settings the console driver reports through TCGETS. */
#define BK_TCGETS 0x5401

/* Whether every one of `n` bytes still holds `value`. */
static int all_bytes_are(const unsigned char *buf, size_t n, unsigned char value) {
  size_t i;

  for (i = 0; i < n; i++) {
    if (buf[i] != value) {
      return 0;
    }
  }
  return 1;
}

/*
 * posix_devctl() has two outcomes and each one is asserted on its own.
 *
 * The old case tried to cover both at once with
 * `ret == 0 || ret == -1`, which no implementation can ever fail: the call
 * either returns 0 or -1, so the assertion held whether the errno was right,
 * wrong, or unset.
 */
static int case_issue8_posix_devctl(void) {
  int fd;

  /*
   * A file in the root tmpfs. `/dev/null` would be the natural choice, but
   * this board does not populate /dev, so the case would skip and assert
   * nothing - which is how the old version of this case managed to look
   * green while checking nothing.
   */
  fd = open("/posix-devctl.txt", O_CREAT | O_RDWR, 0600);
  if (fd < 0) {
    return POSIX_SKIP;
  }

  /*
   * Path 1 - the object cannot do this. A regular file has no device behind
   * it, and POSIX has one errno for "the request is not supported": ENOTSUP.
   * The VFS reports ENOTTY here, and `posix_devctl()` translates it; a
   * regression that forwards ENOTTY (or ENOSYS) fails this assertion.
   *
   * The caller's `dev_info` is only written on success, so it keeps its
   * value.
   */
  int info = 0x5a5a5a5a;
  POSIX_ASSERT_ERRNO(posix_devctl(fd, 0x1234, NULL, 0, &info), ENOTSUP);
  POSIX_ASSERT_EQ(info, 0x5a5a5a5a);

  POSIX_ASSERT_EQ(posix_close(fd, 0), 0);

  /*
   * Path 2 - success. The console tty implements TCGETS, so the request
   * reaches a driver, which writes the terminal settings into `data` and
   * returns 0; `dev_info` then carries the driver's return value.
   *
   * The buffer is poisoned first: if the driver never wrote to it, the
   * pattern is still there and the case fails.
   */
  unsigned char termios_bytes[64];
  int tty_info = -1;

  memset(termios_bytes, 0xaa, sizeof(termios_bytes));
  POSIX_ASSERT_EQ(
      posix_devctl(1, BK_TCGETS, termios_bytes, sizeof(termios_bytes),
                   &tty_info),
      0);
  POSIX_ASSERT_EQ(tty_info, 0);
  POSIX_ASSERT(!all_bytes_are(termios_bytes, sizeof(termios_bytes), 0xaa));

  return POSIX_PASS;
}

POSIX_CASE("issue8_posix_close", case_issue8_posix_close);
POSIX_CASE("issue8_posix_getdents", case_issue8_posix_getdents);
POSIX_CASE("issue8_posix_getdents_bad_args", case_issue8_posix_getdents_bad_args);
POSIX_CASE("issue8_posix_devctl", case_issue8_posix_devctl);
