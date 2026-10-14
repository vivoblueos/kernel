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
 * BlueOS newlib compatibility shim for <sys/ioctl.h>.
 *
 * The toolchain's newlib sysroot has no <sys/ioctl.h>. quickjs-libc.c's
 * os.ttyGetWinSize uses struct winsize + TIOCGWINSZ via ioctl(). The console
 * has no real window size; the call will simply fail at runtime (return -1)
 * and ttyGetWinSize returns null. This header is placed earlier on the include
 * path via the engine's bk_include dir.
 */
#ifndef _BLUEOS_COMPAT_SYS_IOCTL_H
#define _BLUEOS_COMPAT_SYS_IOCTL_H

#ifdef __cplusplus
extern "C" {
#endif

struct winsize {
    unsigned short ws_row;    /* rows, in characters */
    unsigned short ws_col;    /* columns, in characters */
    unsigned short ws_xpixel; /* horizontal size, pixels */
    unsigned short ws_ypixel; /* vertical size, pixels */
};

#define TIOCGWINSZ 0x5413
#define TIOCSWINSZ 0x5414

/* No BlueOS implementation: the call returns -1 (ENOSYS) via the kernel. */
int ioctl(int fd, unsigned long request, ...);

#ifdef __cplusplus
}
#endif

#endif /* _BLUEOS_COMPAT_SYS_IOCTL_H */
