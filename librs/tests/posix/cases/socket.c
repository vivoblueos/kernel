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
#include <unistd.h>

#include "posix_case.h"

/*
 * newlib ships no sys/socket.h (sockets are not part of its syscall set), so
 * the constants and the prototype come from the Linux ABI that librs mirrors.
 * The point of the case is the librs/kernel path, not the header.
 */
#define POSIX_AF_INET 2
#define POSIX_SOCK_STREAM 1
extern int socket(int domain, int type, int protocol);

/*
 * This asserts the allocation and release path only. bind()/listen() on
 * 127.0.0.1 still returns EPROTONOSUPPORT on this build, which is a separate
 * (and already recorded) v1 gap; asserting it here would make the case pass
 * for the wrong reason.
 */
static int run(void) {
  int fd = socket(POSIX_AF_INET, POSIX_SOCK_STREAM, 0);
  POSIX_ASSERT(fd >= 0);
  errno = 0;
  int close_result = close(fd);
  if (close_result != 0) {
    posix_sayf("  close errno ", errno);
  }
  POSIX_ASSERT_EQ(close_result, 0);
  return POSIX_PASS;
}

POSIX_CASE_XFAIL(
    "socket", run,
    "close() of an unbound socket fails: SocketFile::close -> "
    "Connection::shutdown asks the net stack to shut down a socket it never "
    "registered, so releasing a freshly allocated socket returns an error");
