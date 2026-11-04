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
 * Volume statistics and anonymous mappings.
 *
 * Four of these calls used to report success without doing anything:
 * fstatvfs() returned 0 and left the caller's struct untouched, munmap()
 * returned 0 for addresses nobody had mapped, mmap() reported MAP_FAILED with
 * errno == -1, and the kernel's statfs() answered EINVAL for a path that does
 * not exist. None of that is visible from a return code alone, so every case
 * here checks the *content* the call is supposed to produce, not just that it
 * returned 0.
 *
 * newlib has no <sys/statvfs.h> and no <sys/mman.h>; both come from
 * librs/include, which is on the include path ahead of the newlib sysroot.
 */

#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <sys/mman.h>
#include <sys/statvfs.h>
#include <unistd.h>

#include "posix_case.h"

/*
 * Not POSIX: BlueOS's identity syscall, exported as bk_echo() so a case can
 * make one round trip through the syscall path with nothing in between.
 */
extern long bk_echo(long val);

/*
 * The C and Rust definitions of `struct statvfs` have to agree byte for byte,
 * because the kernel fills the POSIX structure from Rust. On LP64 the size is
 * 80 and not 88 only because newlib types fsfilcnt_t as a 32-bit unsigned:
 * that makes f_files..f_favail four-byte fields followed by four bytes of
 * padding before f_fsid. These three assertions are the whole reason that quirk
 * is spelled out in librs/include/sys/statvfs.h instead of `unsigned long`.
 *
 * Only pinned on 64-bit targets, and for the same reason the header itself is
 * written for them: there is no C consumer on rv32 or Cortex-M yet, and the
 * expected offsets there depend on that ABI's 64-bit alignment rules rather
 * than on anything this case can assert.
 */
#if UINTPTR_MAX > 0xffffffffu
_Static_assert(sizeof(struct statvfs) == 80,
               "struct statvfs must match libc::statvfs (80 bytes on LP64)");
_Static_assert(offsetof(struct statvfs, f_files) == 40,
               "f_files must follow three 64-bit block counts");
_Static_assert(offsetof(struct statvfs, f_fsid) == 56,
               "f_fsid must sit after the padded 32-bit inode counts");
#endif

/*
 * Whether this board has a user address space at all.
 *
 * Only rv64 does. On every other target `mmap`/`munmap` compile to an honest
 * ENOSYS, and a case that expected the rv64 errno would fail there for a
 * reason that has nothing to do with the wrapper under test.
 */
#if defined(__riscv) && (__riscv_xlen == 64)
#define MMAP_WITHOUT_A_SPACE_ENOMEM
#endif

/* The root filesystem is tmpfs: 4 KiB blocks, 255-byte names, no mount flags
 * and - because tmpfs reports no capacity - zero blocks. Those values are what
 * makes a wrong translation visible: with the fields at statfs' offsets
 * f_bsize reads f_type (0x01021994) and f_namemax reads f_flags (0). */
#define TMPFS_BLOCK_SIZE 4096
#define TMPFS_NAME_MAX 255

static int statvfs_reports_the_root_filesystem(void) {
  struct statvfs sv;

  POSIX_ASSERT_EQ(statvfs("/", &sv), 0);
  POSIX_ASSERT_EQ(sv.f_bsize, TMPFS_BLOCK_SIZE);
  POSIX_ASSERT_EQ(sv.f_frsize, TMPFS_BLOCK_SIZE);
  POSIX_ASSERT_EQ(sv.f_namemax, TMPFS_NAME_MAX);
  POSIX_ASSERT_EQ(sv.f_flag, 0);

  /* No quota: what is free is free for this caller too. */
  POSIX_ASSERT_EQ(sv.f_favail, sv.f_ffree);

  return POSIX_PASS;
}

static int fstatvfs_agrees_with_statvfs(void) {
  struct statvfs by_path;
  struct statvfs by_fd;
  int fd;

  fd = open("/posix-statvfs.txt", O_CREAT | O_RDWR, 0600);
  if (fd < 0) {
    return POSIX_SKIP;
  }

  POSIX_ASSERT_EQ(statvfs("/", &by_path), 0);
  POSIX_ASSERT_EQ(fstatvfs(fd, &by_fd), 0);

  /*
   * Both paths go through the same translation, so every field but the
   * inode-dependent ones must match. If fstatvfs were still the no-op it used
   * to be, `by_fd` would be uninitialised stack and this would read as noise.
   */
  POSIX_ASSERT_EQ(by_fd.f_bsize, by_path.f_bsize);
  POSIX_ASSERT_EQ(by_fd.f_frsize, by_path.f_frsize);
  POSIX_ASSERT_EQ(by_fd.f_blocks, by_path.f_blocks);
  POSIX_ASSERT_EQ(by_fd.f_namemax, by_path.f_namemax);

  POSIX_ASSERT_EQ(close(fd), 0);
  return POSIX_PASS;
}

static int fstatvfs_rejects_a_closed_descriptor(void) {
  struct statvfs sv;
  int fd;

  fd = open("/posix-statvfs-closed.txt", O_CREAT | O_RDWR, 0600);
  if (fd < 0) {
    return POSIX_SKIP;
  }
  POSIX_ASSERT_EQ(close(fd), 0);

  /* The descriptor is gone, so there is no filesystem to describe. */
  POSIX_ASSERT_ERRNO(fstatvfs(fd, &sv), EBADF);

  return POSIX_PASS;
}

static int statvfs_reports_enoent_for_a_missing_path(void) {
  struct statvfs sv;

  /*
   * Both statfs(2) and POSIX say ENOENT. The kernel used to answer EINVAL
   * here, which describes a malformed path - the caller would go looking for
   * a syntax error in a path that was simply not there.
   */
  POSIX_ASSERT_ERRNO(statvfs("/no-such-directory/statvfs", &sv), ENOENT);

  return POSIX_PASS;
}

static int munmap_refuses_an_unmapped_range(void) {
  /*
   * Nothing in this image ever mapped 0x1000, and this thread has no address
   * space to have mapped it into. Returning 0 here would tell the caller its
   * memory had been released when nothing happened at all.
   */
#ifdef MMAP_WITHOUT_A_SPACE_ENOMEM
  POSIX_ASSERT_ERRNO(munmap((void *)0x1000, 4096), EINVAL);
#else
  POSIX_ASSERT_ERRNO(munmap((void *)0x1000, 4096), ENOSYS);
#endif

  return POSIX_PASS;
}

static int mmap_validates_its_arguments(void) {
  void *addr;

  /*
   * Neither MAP_SHARED nor MAP_PRIVATE: refused before the kernel looks for an
   * address space. This is also the check that the wrapper passes `prot` and
   * `flags` in the right registers - swap them and either this becomes a
   * different errno or the call succeeds.
   */
#ifdef MMAP_WITHOUT_A_SPACE_ENOMEM
  errno = 0;
  addr = mmap(NULL, 4096, PROT_READ, 0, -1, 0);
  POSIX_ASSERT(addr == MAP_FAILED);
  POSIX_ASSERT_EQ(errno, EINVAL);

  /*
   * A well-formed anonymous request. The kernel supports it, but this thread
   * runs in M-mode with no process, so there is nothing to map into and the
   * answer is ENOMEM - not a pointer, and not silence.
   */
  errno = 0;
  addr = mmap(NULL, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS,
              -1, 0);
  POSIX_ASSERT(addr == MAP_FAILED);
  POSIX_ASSERT_EQ(errno, ENOMEM);
#else
  errno = 0;
  addr = mmap(NULL, 4096, PROT_READ, 0, -1, 0);
  POSIX_ASSERT(addr == MAP_FAILED);
  POSIX_ASSERT_EQ(errno, ENOSYS);
#endif

  return POSIX_PASS;
}

static int echo_round_trips_its_argument(void) {
  /* Positive, negative and zero: a wrapper that dropped the sign or returned a
   * constant would pass only the first. */
  POSIX_ASSERT_EQ(bk_echo(0x5a5a), 0x5a5a);
  POSIX_ASSERT_EQ(bk_echo(-7), -7);
  POSIX_ASSERT_EQ(bk_echo(0), 0);

  return POSIX_PASS;
}

POSIX_CASE("statvfs_reports_the_root_filesystem", statvfs_reports_the_root_filesystem);
POSIX_CASE("fstatvfs_agrees_with_statvfs", fstatvfs_agrees_with_statvfs);
POSIX_CASE("fstatvfs_rejects_a_closed_descriptor", fstatvfs_rejects_a_closed_descriptor);
POSIX_CASE("statvfs_reports_enoent_for_a_missing_path", statvfs_reports_enoent_for_a_missing_path);
POSIX_CASE("munmap_refuses_an_unmapped_range", munmap_refuses_an_unmapped_range);
POSIX_CASE("mmap_validates_its_arguments", mmap_validates_its_arguments);
POSIX_CASE("echo_round_trips_its_argument", echo_round_trips_its_argument);
