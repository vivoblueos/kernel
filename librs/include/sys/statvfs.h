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
 * <sys/statvfs.h> for BlueOS.
 *
 * newlib 4.4.0 ships neither this header nor an implementation of
 * statvfs()/fstatvfs(): POSIX volume statistics are simply absent from it.
 * librs implements both, so the declaration has to come from here as well.
 *
 * The field list is POSIX's, and the field *types* are newlib's own
 * fsblkcnt_t / fsfilcnt_t rather than `unsigned long`. That matters: newlib
 * defines fsblkcnt_t as __uint64_t but fsfilcnt_t as __uint32_t, so the
 * structure is not eleven machine words. Writing `unsigned long` here would
 * produce a layout that disagrees with `libc::statvfs` on the Rust side, and
 * the kernel-facing translation would fill the wrong offsets.
 *
 * The case file librs/tests/posix/cases/statvfs.c pins the resulting size
 * (80 bytes on LP64) with _Static_assert, so a change on either side of the
 * boundary breaks the build instead of the data.
 */

#ifndef LIBRS_INCLUDE_SYS_STATVFS_H
#define LIBRS_INCLUDE_SYS_STATVFS_H

#include <sys/types.h>

#ifdef __cplusplus
extern "C" {
#endif

struct statvfs {
  unsigned long f_bsize;  /* Filesystem block size. */
  unsigned long f_frsize; /* Fragment size. */
  fsblkcnt_t f_blocks;    /* Size of fs in f_frsize units. */
  fsblkcnt_t f_bfree;     /* Free blocks. */
  fsblkcnt_t f_bavail;    /* Free blocks available to unprivileged users. */
  fsfilcnt_t f_files;     /* Number of inodes. */
  fsfilcnt_t f_ffree;     /* Free inodes. */
  fsfilcnt_t f_favail;    /* Free inodes available to unprivileged users. */
  unsigned long f_fsid;   /* Filesystem ID. */
  unsigned long f_flag;   /* Mount flags (ST_RDONLY, ST_NOSUID, ...). */
  unsigned long f_namemax; /* Maximum filename length. */
};

int statvfs(const char *path, struct statvfs *buf);
int fstatvfs(int fildes, struct statvfs *buf);

#ifdef __cplusplus
}
#endif

#endif /* LIBRS_INCLUDE_SYS_STATVFS_H */
