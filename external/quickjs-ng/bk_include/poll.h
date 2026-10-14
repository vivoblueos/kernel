/* Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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
 * BlueOS newlib compatibility shim for <poll.h>.
 *
 * The toolchain's newlib sysroot has no <poll.h>. quickjs-libc.c's
 * js_os_poll uses struct pollfd and the POLL* bits. The layout below is the
 * standard 8-byte newlib/Linux pollfd ({int fd; short events; short
 * revents;}); librs's poll() stub in src/syscalls.rs walks exactly this
 * layout. This header is placed earlier on the include path via the engine's
 * bk_include dir.
 */
#ifndef _BLUEOS_COMPAT_POLL_H
#define _BLUEOS_COMPAT_POLL_H

#ifdef __cplusplus
extern "C" {
#endif

typedef unsigned int nfds_t;

struct pollfd {
    int fd;        /* file descriptor */
    short events;  /* requested events */
    short revents; /* returned events */
};

/* requested / returned event bits */
#define POLLIN   0x0001
#define POLLPRI  0x0002
#define POLLOUT  0x0004
#define POLLERR  0x0008
#define POLLHUP  0x0010
#define POLLNVAL 0x0020

/* Implemented (console-only, always-ready) in librs/src/syscalls.rs. */
int poll(struct pollfd *fds, nfds_t nfds, int timeout);

#ifdef __cplusplus
}
#endif

#endif /* _BLUEOS_COMPAT_POLL_H */
