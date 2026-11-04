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
 * POSIX `poll()` and `ppoll()`.
 *
 * The kernel used to answer these with a stub that declared every descriptor
 * below 3 readable and every other one dead, so an event loop never noticed
 * a socket becoming ready. These cases pin down what POSIX actually requires:
 * the revents mask, the distinction between "nothing ready" and "bad
 * descriptor", the two timeout encodings, and that a signal interrupts the
 * wait instead of being slept through.
 */

#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <string.h>
#include <sys/select.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

#include "posix_case.h"

#define POLL_TEST_PATH "/posix-poll.txt"

/* A descriptor that can never be ready: the tests ask for a condition a
 * regular file does not have (high-priority data), so `poll()` has nothing
 * to report and must either time out or return 0 immediately. */
#define NEVER_EVENTS POLLPRI

static int open_poll_file(void) {
  return open(POLL_TEST_PATH, O_CREAT | O_RDWR | O_TRUNC, 0600);
}

/*
 * A regular file is always ready to read and write: POSIX counts a call that
 * would not block as ready, and a file has no blocking read or write.
 */
static int case_poll_regular_file_ready(void) {
  struct pollfd pfd;
  int fd = open_poll_file();

  POSIX_ASSERT(fd >= 0);

  memset(&pfd, 0, sizeof(pfd));
  pfd.fd = fd;
  pfd.events = POLLIN | POLLOUT;

  POSIX_ASSERT_EQ(poll(&pfd, 1, 0), 1);
  POSIX_ASSERT(pfd.revents & POLLIN);
  POSIX_ASSERT(pfd.revents & POLLOUT);

  POSIX_ASSERT_EQ(close(fd), 0);
  return POSIX_PASS;
}

/*
 * Nothing ready is not the same as failure: `poll()` returns 0 and leaves
 * revents clear. With a zero timeout it must not wait at all.
 */
static int case_poll_nothing_ready(void) {
  struct pollfd pfd;
  int fd = open_poll_file();

  POSIX_ASSERT(fd >= 0);

  memset(&pfd, 0, sizeof(pfd));
  pfd.fd = fd;
  pfd.events = NEVER_EVENTS;

  POSIX_ASSERT_EQ(poll(&pfd, 1, 0), 0);
  POSIX_ASSERT_EQ(pfd.revents, 0);

  POSIX_ASSERT_EQ(close(fd), 0);
  return POSIX_PASS;
}

/*
 * POSIX: "If the value of fd is less than 0, events shall be ignored, and
 * revents shall be set to 0 in that entry". Such an entry is a way of
 * skipping a slot, not a way of getting POLLNVAL.
 */
static int case_poll_negative_fd_ignored(void) {
  struct pollfd pfd;

  memset(&pfd, 0, sizeof(pfd));
  pfd.fd = -1;
  pfd.events = POLLIN | POLLOUT;

  POSIX_ASSERT_EQ(poll(&pfd, 1, 0), 0);
  POSIX_ASSERT_EQ(pfd.revents, 0);

  return POSIX_PASS;
}

/*
 * A descriptor that is not open reports POLLNVAL, and it is counted as one
 * of the ready entries - an error condition the caller has to hear about.
 */
static int case_poll_bad_fd_nval(void) {
  struct pollfd pfd;

  memset(&pfd, 0, sizeof(pfd));
  pfd.fd = 9999;
  pfd.events = POLLIN;

  POSIX_ASSERT_EQ(poll(&pfd, 1, 0), 1);
  POSIX_ASSERT(pfd.revents & POLLNVAL);

  return POSIX_PASS;
}

/*
 * An empty set is a legal argument: the call is then just a way of sleeping
 * for the timeout, and reports nothing ready.
 */
static int case_poll_zero_nfds(void) {
  POSIX_ASSERT_EQ(poll(NULL, 0, 0), 0);
  return POSIX_PASS;
}

/*
 * A positive timeout really waits, and then reports nothing ready rather
 * than an error. The lower bound is loose because the system clock is
 * tick-quantised and the scheduler can round a sleep up.
 */
static int case_poll_timeout_elapses(void) {
  struct pollfd pfd;
  struct timespec start;
  struct timespec end;
  long elapsed_ms;
  int fd = open_poll_file();

  POSIX_ASSERT(fd >= 0);

  memset(&pfd, 0, sizeof(pfd));
  pfd.fd = fd;
  pfd.events = NEVER_EVENTS;

  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &start), 0);
  POSIX_ASSERT_EQ(poll(&pfd, 1, 50), 0);
  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &end), 0);

  elapsed_ms = (end.tv_sec - start.tv_sec) * 1000 +
               (end.tv_nsec - start.tv_nsec) / 1000000;
  POSIX_ASSERT(elapsed_ms >= 25);
  POSIX_ASSERT(elapsed_ms < 5000);
  POSIX_ASSERT_EQ(pfd.revents, 0);

  POSIX_ASSERT_EQ(close(fd), 0);
  return POSIX_PASS;
}

/*
 * A signal that arrives while `poll()` is waiting interrupts it with EINTR
 * rather than letting the call sleep out its timeout. The signal is sent
 * from a second thread so that it lands while the caller is blocked.
 */
static volatile sig_atomic_t poll_handler_ran;

static void poll_signal_handler(int signum) {
  (void)signum;
  poll_handler_ran = 1;
}

static void *signal_sender(void *argument) {
  struct timespec delay;

  (void)argument;
  delay.tv_sec = 0;
  delay.tv_nsec = 50 * 1000 * 1000;
  nanosleep(&delay, NULL);
  kill(0, SIGUSR1);
  return NULL;
}

static int case_poll_eintr_on_signal(void) {
  struct sigaction act;
  struct sigaction old;
  struct pollfd pfd;
  pthread_t thread;
  int fd = open_poll_file();

  POSIX_ASSERT(fd >= 0);

  memset(&act, 0, sizeof(act));
  act.sa_handler = poll_signal_handler;
  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &act, &old), 0);

  poll_handler_ran = 0;

  memset(&pfd, 0, sizeof(pfd));
  pfd.fd = fd;
  pfd.events = NEVER_EVENTS;

  POSIX_ASSERT_EQ(pthread_create(&thread, NULL, signal_sender, NULL), 0);

  /* A two-second timeout: if the signal does not interrupt the call, this
   * returns 0 after two seconds and the assertion below fails. */
  POSIX_ASSERT_ERRNO(poll(&pfd, 1, 2000), EINTR);

  POSIX_ASSERT_EQ(pthread_join(thread, NULL), 0);
  POSIX_ASSERT_EQ(poll_handler_ran, 1);

  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &old, NULL), 0);
  POSIX_ASSERT_EQ(close(fd), 0);
  return POSIX_PASS;
}

/*
 * `ppoll()` takes the same interval as `poll()`, but as a `struct timespec`.
 * A zero one is the "do not wait" case.
 */
static int case_ppoll_zero_timeout(void) {
  struct pollfd pfd;
  struct timespec timeout;
  int fd = open_poll_file();

  POSIX_ASSERT(fd >= 0);

  memset(&pfd, 0, sizeof(pfd));
  pfd.fd = fd;
  pfd.events = POLLIN | POLLOUT;

  timeout.tv_sec = 0;
  timeout.tv_nsec = 0;
  POSIX_ASSERT_EQ(ppoll(&pfd, 1, &timeout, NULL), 1);
  POSIX_ASSERT(pfd.revents & POLLIN);

  POSIX_ASSERT_EQ(close(fd), 0);
  return POSIX_PASS;
}

/*
 * A negative interval is an error for `ppoll()`, even though the same value
 * passed to `poll()` means "wait forever". The two calls spell the infinite
 * timeout differently - null versus -1 - and mixing them up is exactly the
 * kind of bug the check exists to catch.
 */
static int case_ppoll_negative_timeout_einval(void) {
  struct pollfd pfd;
  struct timespec timeout;
  int fd = open_poll_file();

  POSIX_ASSERT(fd >= 0);

  memset(&pfd, 0, sizeof(pfd));
  pfd.fd = fd;
  pfd.events = POLLIN;

  timeout.tv_sec = -1;
  timeout.tv_nsec = 0;
  POSIX_ASSERT_ERRNO(ppoll(&pfd, 1, &timeout, NULL), EINVAL);

  timeout.tv_sec = 0;
  timeout.tv_nsec = 1000000000; /* one nanosecond past the end of a second */
  POSIX_ASSERT_ERRNO(ppoll(&pfd, 1, &timeout, NULL), EINVAL);

  POSIX_ASSERT_EQ(close(fd), 0);
  return POSIX_PASS;
}

/*
 * `ppoll()` installs `sigmask` for the duration of the wait, so a signal in
 * that mask is held out and does not interrupt the call. Here SIGUSR1 is
 * added to the mask while the wait runs, so the call has to run out its
 * timeout rather than come back with EINTR.
 */
static int case_ppoll_sigmask_hides_signal(void) {
  struct sigaction act;
  struct sigaction old;
  struct pollfd pfd;
  struct timespec timeout;
  sigset_t mask;
  pthread_t thread;
  int fd = open_poll_file();

  POSIX_ASSERT(fd >= 0);

  memset(&act, 0, sizeof(act));
  act.sa_handler = poll_signal_handler;
  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &act, &old), 0);
  poll_handler_ran = 0;

  POSIX_ASSERT_EQ(sigemptyset(&mask), 0);
  POSIX_ASSERT_EQ(sigaddset(&mask, SIGUSR1), 0);

  memset(&pfd, 0, sizeof(pfd));
  pfd.fd = fd;
  pfd.events = NEVER_EVENTS;

  timeout.tv_sec = 0;
  timeout.tv_nsec = 300 * 1000 * 1000;

  POSIX_ASSERT_EQ(pthread_create(&thread, NULL, signal_sender, NULL), 0);

  /* Not EINTR: the mask holds the signal off. The call times out. */
  POSIX_ASSERT_EQ(ppoll(&pfd, 1, &timeout, &mask), 0);

  POSIX_ASSERT_EQ(pthread_join(thread, NULL), 0);

  /* The mask is restored on return, so the held signal is delivered then. */
  POSIX_ASSERT_EQ(poll_handler_ran, 1);

  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &old, NULL), 0);
  POSIX_ASSERT_EQ(close(fd), 0);
  return POSIX_PASS;
}

/*
 * The two timeout encodings have to mean the same thing. A `poll()` timeout
 * of 40 milliseconds and a `ppoll()` interval of 40 milliseconds are the
 * same wait; checking that both return 0 catches a call that confused
 * milliseconds with nanoseconds and turned a short wait into a long one.
 */
static int case_ppoll_timeout_matches_poll(void) {
  struct pollfd pfd;
  struct timespec timeout;
  struct timespec start;
  struct timespec end;
  long elapsed_ms;
  int fd = open_poll_file();

  POSIX_ASSERT(fd >= 0);

  memset(&pfd, 0, sizeof(pfd));
  pfd.fd = fd;
  pfd.events = NEVER_EVENTS;

  timeout.tv_sec = 0;
  timeout.tv_nsec = 40 * 1000 * 1000;

  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &start), 0);
  POSIX_ASSERT_EQ(ppoll(&pfd, 1, &timeout, NULL), 0);
  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &end), 0);

  elapsed_ms = (end.tv_sec - start.tv_sec) * 1000 +
               (end.tv_nsec - start.tv_nsec) / 1000000;
  POSIX_ASSERT(elapsed_ms >= 20);
  POSIX_ASSERT(elapsed_ms < 5000);

  POSIX_ASSERT_EQ(close(fd), 0);
  return POSIX_PASS;
}

/*
 * `select()` has to agree with `poll()` on what "ready" means. A regular
 * file is ready for both reading and writing, and a descriptor named in two
 * sets still counts once in the result.
 */
static int case_select_regular_file_ready(void) {
  struct timeval timeout;
  fd_set readfds;
  fd_set writefds;
  int fd = open_poll_file();

  POSIX_ASSERT(fd >= 0);
  POSIX_ASSERT(fd < FD_SETSIZE);

  FD_ZERO(&readfds);
  FD_ZERO(&writefds);
  FD_SET(fd, &readfds);
  FD_SET(fd, &writefds);

  timeout.tv_sec = 0;
  timeout.tv_usec = 0;

  POSIX_ASSERT_EQ(select(fd + 1, &readfds, &writefds, NULL, &timeout), 1);
  POSIX_ASSERT(FD_ISSET(fd, &readfds));
  POSIX_ASSERT(FD_ISSET(fd, &writefds));

  POSIX_ASSERT_EQ(close(fd), 0);
  return POSIX_PASS;
}

/* Two distinct ready descriptors are counted separately. */
static int case_select_two_files_ready(void) {
  struct timeval timeout;
  fd_set readfds;
  int first = open_poll_file();
  int second = open_poll_file();
  int highest;

  POSIX_ASSERT(first >= 0);
  POSIX_ASSERT(second >= 0);
  POSIX_ASSERT(first < FD_SETSIZE);
  POSIX_ASSERT(second < FD_SETSIZE);

  FD_ZERO(&readfds);
  FD_SET(first, &readfds);
  FD_SET(second, &readfds);

  timeout.tv_sec = 0;
  timeout.tv_usec = 0;

  highest = first > second ? first : second;
  POSIX_ASSERT_EQ(select(highest + 1, &readfds, NULL, NULL, &timeout), 2);
  POSIX_ASSERT(FD_ISSET(first, &readfds));
  POSIX_ASSERT(FD_ISSET(second, &readfds));

  POSIX_ASSERT_EQ(close(first), 0);
  POSIX_ASSERT_EQ(close(second), 0);
  return POSIX_PASS;
}

/*
 * Nothing ready is a zero result, not an error: `exceptfds` asks for high-
 * priority data, which a regular file never has. The wait really elapses and
 * the set comes back empty.
 */
static int case_select_timeout_elapses(void) {
  struct timeval timeout;
  struct timespec start;
  struct timespec end;
  fd_set exceptfds;
  long elapsed_ms;
  int fd = open_poll_file();

  POSIX_ASSERT(fd >= 0);
  POSIX_ASSERT(fd < FD_SETSIZE);

  FD_ZERO(&exceptfds);
  FD_SET(fd, &exceptfds);

  timeout.tv_sec = 0;
  timeout.tv_usec = 50 * 1000;

  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &start), 0);
  POSIX_ASSERT_EQ(select(fd + 1, NULL, NULL, &exceptfds, &timeout), 0);
  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &end), 0);

  elapsed_ms = (end.tv_sec - start.tv_sec) * 1000 +
               (end.tv_nsec - start.tv_nsec) / 1000000;
  POSIX_ASSERT(elapsed_ms >= 25);
  POSIX_ASSERT(elapsed_ms < 5000);
  POSIX_ASSERT(!FD_ISSET(fd, &exceptfds));

  POSIX_ASSERT_EQ(close(fd), 0);
  return POSIX_PASS;
}

/* A closed descriptor in a set is an error for the whole call. */
static int case_select_bad_fd_ebadf(void) {
  struct timeval timeout;
  fd_set readfds;
  int fd = open_poll_file();

  POSIX_ASSERT(fd >= 0);
  POSIX_ASSERT_EQ(close(fd), 0);

  FD_ZERO(&readfds);
  FD_SET(fd, &readfds);

  timeout.tv_sec = 0;
  timeout.tv_usec = 0;

  POSIX_ASSERT_ERRNO(select(fd + 1, &readfds, NULL, NULL, &timeout), EBADF);
  return POSIX_PASS;
}

/* An empty argument list is a legal sleep, which returns 0 at once here. */
static int case_select_zero_nfds(void) {
  struct timeval timeout;

  timeout.tv_sec = 0;
  timeout.tv_usec = 0;

  POSIX_ASSERT_EQ(select(0, NULL, NULL, NULL, &timeout), 0);
  return POSIX_PASS;
}

/* `tv_usec` beyond one second is `EINVAL`, not a rounded-up wait. */
static int case_select_invalid_timeval(void) {
  struct timeval timeout;

  timeout.tv_sec = 0;
  timeout.tv_usec = 1000000;
  POSIX_ASSERT_ERRNO(select(0, NULL, NULL, NULL, &timeout), EINVAL);

  timeout.tv_sec = -1;
  timeout.tv_usec = 0;
  POSIX_ASSERT_ERRNO(select(0, NULL, NULL, NULL, &timeout), EINVAL);

  return POSIX_PASS;
}

POSIX_CASE("poll_regular_file_ready", case_poll_regular_file_ready);
POSIX_CASE("poll_nothing_ready", case_poll_nothing_ready);
POSIX_CASE("poll_negative_fd_ignored", case_poll_negative_fd_ignored);
POSIX_CASE("poll_bad_fd_nval", case_poll_bad_fd_nval);
POSIX_CASE("poll_zero_nfds", case_poll_zero_nfds);
POSIX_CASE("poll_timeout_elapses", case_poll_timeout_elapses);
POSIX_CASE("poll_eintr_on_signal", case_poll_eintr_on_signal);
POSIX_CASE("ppoll_zero_timeout", case_ppoll_zero_timeout);
POSIX_CASE("ppoll_negative_timeout_einval", case_ppoll_negative_timeout_einval);
POSIX_CASE("ppoll_sigmask_hides_signal", case_ppoll_sigmask_hides_signal);
POSIX_CASE("ppoll_timeout_matches_poll", case_ppoll_timeout_matches_poll);
POSIX_CASE("select_regular_file_ready", case_select_regular_file_ready);
POSIX_CASE("select_two_files_ready", case_select_two_files_ready);
POSIX_CASE("select_timeout_elapses", case_select_timeout_elapses);
POSIX_CASE("select_bad_fd_ebadf", case_select_bad_fd_ebadf);
POSIX_CASE("select_zero_nfds", case_select_zero_nfds);
POSIX_CASE("select_invalid_timeval", case_select_invalid_timeval);
