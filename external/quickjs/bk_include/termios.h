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
 * BlueOS newlib compatibility shim for <termios.h>.
 *
 * The toolchain's newlib sysroot ships a bare <termios.h> that only does
 * #include <sys/termios.h>, but that file is not present, so the struct
 * termios definition and the IGNBRK/VMIN/... constants quickjs-libc.c needs
 * for os.ttySetRaw are unavailable. Provide them here. This header is placed
 * earlier on the include path (via the engine's bk_include dir) so it
 * shadows the dangling toolchain <termios.h>.
 *
 * The console has no line discipline: librs's tcgetattr/tcsetattr stubs are
 * no-ops, so these flag manipulations never take effect at runtime. Only the
 * type layout and constant names matter for compilation.
 */
#ifndef _BLUEOS_COMPAT_TERMIOS_H
#define _BLUEOS_COMPAT_TERMIOS_H

#ifdef __cplusplus
extern "C" {
#endif

typedef unsigned int tcflag_t;
typedef unsigned char cc_t;
typedef unsigned int speed_t;

#define NCCS 19

struct termios {
    tcflag_t c_iflag; /* input modes   */
    tcflag_t c_oflag; /* output modes  */
    tcflag_t c_cflag; /* control modes */
    tcflag_t c_lflag; /* local modes   */
    cc_t c_line;      /* line discipline */
    cc_t c_cc[NCCS];  /* control characters */
};

/* c_iflag bits */
#define IGNBRK  0x0001
#define BRKINT  0x0002
#define IGNPAR  0x0004
#define PARMRK  0x0008
#define INPCK   0x0010
#define ISTRIP  0x0020
#define INLCR   0x0040
#define IGNCR   0x0080
#define ICRNL   0x0100
#define IXON    0x0400
#define IXOFF   0x1000

/* c_oflag bits */
#define OPOST   0x0001
#define ONLCR   0x0002

/* c_cflag bits */
#define CSIZE   0x0030
#define CS5     0x0000
#define CS6     0x0010
#define CS7     0x0020
#define CS8     0x0030
#define CSTOPB  0x0040
#define CREAD   0x0080
#define PARENB  0x0100
#define PARODD  0x0200
#define HUPCL   0x0400

/* c_lflag bits */
#define ISIG    0x0001
#define ICANON  0x0002
#define ECHO    0x0008
#define ECHOE   0x0010
#define ECHOK   0x0020
#define ECHONL  0x0040
#define NOFLSH  0x0080
#define IEXTEN  0x0100
#define TOSTOP  0x0200

/* c_cc indices */
#define VEOF    0
#define VEOL    1
#define VERASE  2
#define VINTR   3
#define VKILL   4
#define VMIN    5
#define VQUIT   6
#define VSTART  7
#define VSTOP   8
#define VSUSP   9
#define VTIME   10

/* tcsetattr actions */
#define TCSANOW   0
#define TCSADRAIN 1
#define TCSAFLUSH 2

/* tcflush queue selectors */
#define TCIFLUSH  0
#define TCOFLUSH  1
#define TCIOFLUSH 2

/* Implementations are no-op stubs in librs/src/syscalls.rs. */
int tcgetattr(int fd, struct termios *termios_p);
int tcsetattr(int fd, int action, const struct termios *termios_p);
speed_t cfgetispeed(const struct termios *termios_p);
speed_t cfgetospeed(const struct termios *termios_p);
int cfsetispeed(struct termios *termios_p, speed_t speed);
int cfsetospeed(struct termios *termios_p, speed_t speed);

#ifdef __cplusplus
}
#endif

#endif /* _BLUEOS_COMPAT_TERMIOS_H */
