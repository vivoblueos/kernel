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
 * The POSIX.1-2024 (Issue 8) interfaces that newlib 4.4.0 does not declare.
 *
 * newlib ships the *implementation* of some Issue 8 functions (memmem,
 * strlcpy, qsort_r, sig2str, ...) but not all of them, and the ones it does
 * not ship are also the ones it does not declare. A C program that wants to
 * call timespec_get() or sem_clockwait() therefore fails to compile with
 * "implicit declaration", which in C11 is an error rather than a warning.
 *
 * This header declares the missing ones. It is included by the POSIX
 * conformance cases; the implementation lives in librs (Rust).
 *
 * The prototypes follow IEEE Std 1003.1-2024 exactly:
 *
 *   int      timespec_get(struct timespec *, clockid_t);
 *   int      sem_clockwait(sem_t *, clockid_t, const struct timespec *);
 *   int      posix_close(int, int);
 *   int      posix_devctl(int, int, void *, size_t, int *);
 *   ssize_t  posix_getdents(int, void *, size_t, int);
 */

#ifndef LIBRS_INCLUDE_POSIX_ISSUE8_H
#define LIBRS_INCLUDE_POSIX_ISSUE8_H

#include <semaphore.h>
#include <stddef.h>
#include <sys/types.h>
#include <time.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * POSIX.1-2024 XSH 2.3.1: the value of POSIX_CLOSE_RESTART. This
 * implementation does not restart an interrupted close, so the value is 0 -
 * which also means posix_close() never fails with EINTR.
 */
#ifndef POSIX_CLOSE_RESTART
#define POSIX_CLOSE_RESTART 0
#endif

/*
 * The `posix_dent` structure that posix_getdents() fills in.
 *
 * POSIX defines `d_name` as a flexible array member, so the structure's
 * size is the size of the fixed part. `d_reclen` gives the number of bytes
 * each entry occupies in the buffer, including padding.
 */
struct posix_dent {
  ino_t d_ino;
  unsigned short d_reclen;
  unsigned char d_type;
  char d_name[];
};

/* The file types posix_getdents() may report in d_type. */
#ifndef DT_UNKNOWN
#define DT_UNKNOWN 0
#endif
#ifndef DT_FIFO
#define DT_FIFO 1
#endif
#ifndef DT_CHR
#define DT_CHR 2
#endif
#ifndef DT_DIR
#define DT_DIR 4
#endif
#ifndef DT_BLK
#define DT_BLK 6
#endif
#ifndef DT_REG
#define DT_REG 8
#endif
#ifndef DT_LNK
#define DT_LNK 10
#endif
#ifndef DT_SOCK
#define DT_SOCK 12
#endif

/*
 * Issue 8 D.1: timespec_get() stores the current time of `base` in `ts` and
 * returns `base`, or -1 if the clock is not supported.
 */
int timespec_get(struct timespec *ts, clockid_t base);

/*
 * Issue 8 C.2: posix_close() closes `fildes` with an explicit restart
 * policy. See POSIX_CLOSE_RESTART above.
 */
int posix_close(int fildes, int flag);

/*
 * Issue 8 C.3: posix_devctl() passes a device control command to the driver
 * behind `fildes`.
 */
int posix_devctl(int fildes, int dcmd, void *restrict dev_data_ptr,
                 size_t nbyte, int *restrict dev_info_ptr);

/*
 * Issue 8 C.4: posix_getdents() reads directory entries into `buf` in the
 * POSIX `posix_dent` format.
 */
ssize_t posix_getdents(int fildes, void *buf, size_t nbyte, int flags);

#ifdef __cplusplus
}
#endif

#endif /* LIBRS_INCLUDE_POSIX_ISSUE8_H */
