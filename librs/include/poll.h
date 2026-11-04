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
 * <poll.h> for POSIX.1-2024 `poll()` and `ppoll()`.
 *
 * The toolchain's newlib sysroot has no <poll.h> at all, so a program that
 * wants to multiplex on descriptors cannot even name the type it has to
 * pass. This header declares it. The layout of `struct pollfd` and the
 * values of the POLL* bits are fixed here and have to match the kernel's
 * `kernel/kernel/src/vfs/poll.rs`, which is what fills `revents` in.
 *
 * The event bits use the same values as the newlib-compatible shim in
 * external/quickjs-ng/bk_include/poll.h, so both headers agree.
 */

#ifndef LIBRS_INCLUDE_POLL_H
#define LIBRS_INCLUDE_POLL_H

#include <signal.h>
#include <sys/types.h>
#include <time.h>

#ifdef __cplusplus
extern "C" {
#endif

/* POSIX: the type of the descriptor count. newlib's shim uses unsigned int. */
typedef unsigned int nfds_t;

struct pollfd {
  int fd;        /* file descriptor */
  short events;  /* requested events */
  short revents; /* returned events */
};

/* Requested and returned event bits. */
#define POLLIN   0x0001 /* ready to read */
#define POLLPRI  0x0002 /* high-priority data to read */
#define POLLOUT  0x0004 /* ready to write */
#define POLLERR  0x0008 /* error (returned only) */
#define POLLHUP  0x0010 /* hangup (returned only) */
#define POLLNVAL 0x0020 /* invalid descriptor (returned only) */

/*
 * POSIX.1-2024: `poll()` takes the timeout in milliseconds, where a
 * negative value means "wait forever". `ppoll()` takes the same interval
 * as a `struct timespec`, plus a signal mask that replaces the thread's
 * own for the duration of the wait - a null mask means "change nothing",
 * and a null timeout means "wait forever" (where `poll()` would use -1).
 */
int poll(struct pollfd *fds, nfds_t nfds, int timeout);
int ppoll(struct pollfd *fds, nfds_t nfds, const struct timespec *timeout,
          const sigset_t *sigmask);

#ifdef __cplusplus
}
#endif

#endif /* LIBRS_INCLUDE_POLL_H */
