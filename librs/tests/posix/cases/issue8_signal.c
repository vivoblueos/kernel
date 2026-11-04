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
 * The POSIX signal interfaces.
 *
 * The kernel used to answer every one of these calls with a bare `0`, so a
 * program that installed a handler saw it never run. These cases check the
 * parts POSIX pins down: the disposition table, the per-thread mask, the
 * pending set, and that a handler really runs.
 */

#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include "posix_case.h"

/*
 * Calls the C library's own `sigaddset()` implementation, not newlib's
 * macro, so that the error path can be checked.
 *
 * newlib declares `sigaddset()` as a function and *also* defines a macro of
 * the same name. The macro wins at every use of the name - including in a
 * function declaration - so the function has to be reached through a name
 * the macro cannot expand.
 */
extern int newlib_sigaddset(sigset_t *set, int signo)
    __asm__("sigaddset");

static int librs_sigaddset_check(sigset_t *set, int signo) {
  return newlib_sigaddset(set, signo);
}

/* Set by the handler, so the test can tell that it ran. */
static volatile sig_atomic_t handler_ran;
static volatile sig_atomic_t handler_signum;

static void test_handler(int signum) {
  handler_signum = signum;
  handler_ran = 1;
}

/*
 * `sigaction()` installs a disposition and reports the previous one.
 *
 * POSIX: the call returns 0 on success. The old disposition is written
 * through `oact`.
 */
static int case_signal_sigaction(void) {
  struct sigaction act;
  struct sigaction old;
  struct sigaction old2;

  memset(&act, 0, sizeof(act));
  memset(&old, 0, sizeof(old));
  act.sa_handler = test_handler;

  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &act, &old), 0);

  /* The previous disposition of a signal nobody touched is SIG_DFL. */
  POSIX_ASSERT(old.sa_handler == SIG_DFL || old.sa_handler == SIG_IGN);

  /* Installing again reports what was there before: our handler. */
  POSIX_ASSERT_EQ(sigaction(SIGUSR1, NULL, &old2), 0);
  POSIX_ASSERT_EQ(old2.sa_handler, test_handler);

  /* Put the default disposition back so a later case is not affected. */
  act.sa_handler = SIG_DFL;
  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &act, NULL), 0);

  return POSIX_PASS;
}

/*
 * `sigaction()` rejects a signal number that does not exist.
 */
static int case_signal_sigaction_bad_signum(void) {
  struct sigaction act;

  memset(&act, 0, sizeof(act));
  act.sa_handler = test_handler;

  POSIX_ASSERT_ERRNO(sigaction(0, &act, NULL), EINVAL);
  POSIX_ASSERT_ERRNO(sigaction(-1, &act, NULL), EINVAL);
  POSIX_ASSERT_ERRNO(sigaction(9999, &act, NULL), EINVAL);

  return POSIX_PASS;
}

/*
 * `sigprocmask()` changes the mask of the calling thread and reports the
 * previous one.
 *
 * POSIX: SIG_BLOCK adds, SIG_UNBLOCK removes, SIG_SETMASK replaces.
 */
static int case_signal_sigprocmask(void) {
  sigset_t set;
  sigset_t old;
  sigset_t now;

  sigemptyset(&set);
  sigaddset(&set, SIGUSR1);

  /* Start from a known state: nothing blocked. */
  POSIX_ASSERT_EQ(sigprocmask(SIG_SETMASK, NULL, &old), 0);
  POSIX_ASSERT_EQ(sigismember(&old, SIGUSR1), 0);

  /* Blocking reports the previous mask, which must not contain SIGUSR1. */
  POSIX_ASSERT_EQ(sigprocmask(SIG_BLOCK, &set, &old), 0);
  POSIX_ASSERT_EQ(sigismember(&old, SIGUSR1), 0);

  /* Now SIGUSR1 is blocked. */
  POSIX_ASSERT_EQ(sigprocmask(SIG_SETMASK, NULL, &now), 0);
  POSIX_ASSERT_EQ(sigismember(&now, SIGUSR1), 1);

  /* Unblocking reports the previous mask, which did contain SIGUSR1. */
  POSIX_ASSERT_EQ(sigprocmask(SIG_UNBLOCK, &set, &old), 0);
  POSIX_ASSERT_EQ(sigismember(&old, SIGUSR1), 1);

  POSIX_ASSERT_EQ(sigprocmask(SIG_SETMASK, NULL, &now), 0);
  POSIX_ASSERT_EQ(sigismember(&now, SIGUSR1), 0);

  return POSIX_PASS;
}

/*
 * `sigprocmask()` rejects an unknown operation.
 */
static int case_signal_sigprocmask_bad_how(void) {
  sigset_t set;

  sigemptyset(&set);
  POSIX_ASSERT_ERRNO(sigprocmask(12345, &set, NULL), EINVAL);

  return POSIX_PASS;
}

/*
 * `sigemptyset()`, `sigaddset()`, `sigdelset()` and `sigismember()`
 * manipulate the signal set.
 */
static int case_signal_set_operations(void) {
  sigset_t set;

  POSIX_ASSERT_EQ(sigemptyset(&set), 0);
  POSIX_ASSERT_EQ(sigismember(&set, SIGUSR1), 0);

  POSIX_ASSERT_EQ(sigaddset(&set, SIGUSR1), 0);
  POSIX_ASSERT_EQ(sigismember(&set, SIGUSR1), 1);

  POSIX_ASSERT_EQ(sigdelset(&set, SIGUSR1), 0);
  POSIX_ASSERT_EQ(sigismember(&set, SIGUSR1), 0);

  /*
   * A signal number of zero is not a signal. newlib spells `sigaddset()`
   * as the macro `(*(what) |= (1 << (sig)), 0)`, which neither rejects a
   * zero signal number nor reports an error - so the check has to be made
   * on the library's own function rather than on the macro.
   */
  POSIX_ASSERT_ERRNO(librs_sigaddset_check(&set, 0), EINVAL);

  return POSIX_PASS;
}

/*
 * A handler installed with `sigaction()` actually runs when the signal is
 * raised.
 *
 * This is the core of the signal implementation: before it, the kernel
 * answered `sigaction()` with 0 and never called the handler.
 */
static int case_signal_handler_runs(void) {
  struct sigaction act;

  memset(&act, 0, sizeof(act));
  act.sa_handler = test_handler;

  handler_ran = 0;
  handler_signum = 0;

  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &act, NULL), 0);
  POSIX_ASSERT_EQ(raise(SIGUSR1), 0);

  /*
   * `raise()` delivers the signal to the calling thread; the handler runs
   * at the next scheduling point, which `raise()` itself is.
   */
  POSIX_ASSERT_EQ(handler_ran, 1);
  POSIX_ASSERT_EQ(handler_signum, SIGUSR1);

  act.sa_handler = SIG_DFL;
  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &act, NULL), 0);

  return POSIX_PASS;
}

/*
 * A signal that is blocked stays pending until it is unblocked.
 *
 * POSIX: `sigprocmask()` with SIG_BLOCK on a signal that has no handler
 * running keeps it pending; `sigpending()` reports it.
 */
static int case_signal_blocked_stays_pending(void) {
  struct sigaction act;
  sigset_t set;
  sigset_t pending;

  memset(&act, 0, sizeof(act));
  act.sa_handler = test_handler;

  handler_ran = 0;

  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &act, NULL), 0);

  /* Block SIGUSR1, then raise it. */
  sigemptyset(&set);
  sigaddset(&set, SIGUSR1);
  POSIX_ASSERT_EQ(sigprocmask(SIG_BLOCK, &set, NULL), 0);

  POSIX_ASSERT_EQ(raise(SIGUSR1), 0);

  /* The handler must not have run: the signal is blocked. */
  POSIX_ASSERT_EQ(handler_ran, 0);

  /* The signal is pending. */
  POSIX_ASSERT_EQ(sigpending(&pending), 0);
  POSIX_ASSERT_EQ(sigismember(&pending, SIGUSR1), 1);

  /* Unblocking it lets the handler run. */
  POSIX_ASSERT_EQ(sigprocmask(SIG_UNBLOCK, &set, NULL), 0);
  POSIX_ASSERT_EQ(handler_ran, 1);

  /*
   * Once delivered it is no longer pending, and a signal raised while it is
   * *not* blocked is delivered at the next scheduling point rather than
   * reported by `sigpending()`: "pending" means "raised while blocked".
   */
  POSIX_ASSERT_EQ(sigpending(&pending), 0);
  POSIX_ASSERT_EQ(sigismember(&pending, SIGUSR1), 0);

  handler_ran = 0;
  POSIX_ASSERT_EQ(raise(SIGUSR1), 0);
  POSIX_ASSERT_EQ(sigpending(&pending), 0);
  POSIX_ASSERT_EQ(sigismember(&pending, SIGUSR1), 0);
  POSIX_ASSERT_EQ(handler_ran, 1);

  act.sa_handler = SIG_DFL;
  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &act, NULL), 0);

  return POSIX_PASS;
}

/*
 * `sigpending()` reports nothing when no signal is pending.
 */
static int case_signal_sigpending_empty(void) {
  sigset_t pending;

  POSIX_ASSERT_EQ(sigpending(&pending), 0);
  POSIX_ASSERT_EQ(sigismember(&pending, SIGUSR1), 0);
  POSIX_ASSERT_EQ(sigismember(&pending, SIGUSR2), 0);

  return POSIX_PASS;
}

/*
 * `kill()` with pid 0 sends the signal to the calling process.
 */
static int case_signal_kill_self(void) {
  struct sigaction act;

  memset(&act, 0, sizeof(act));
  act.sa_handler = test_handler;

  handler_ran = 0;

  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &act, NULL), 0);
  POSIX_ASSERT_EQ(kill(0, SIGUSR1), 0);
  POSIX_ASSERT_EQ(handler_ran, 1);
  POSIX_ASSERT_EQ(handler_signum, SIGUSR1);

  act.sa_handler = SIG_DFL;
  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &act, NULL), 0);

  return POSIX_PASS;
}

/*
 * `kill()` rejects a signal number that does not exist.
 */
static int case_signal_kill_bad_signum(void) {
  POSIX_ASSERT_ERRNO(kill(0, 0), EINVAL);
  POSIX_ASSERT_ERRNO(kill(0, 9999), EINVAL);

  return POSIX_PASS;
}

POSIX_CASE("signal_sigaction", case_signal_sigaction);
POSIX_CASE("signal_sigaction_bad_signum", case_signal_sigaction_bad_signum);
POSIX_CASE("signal_sigprocmask", case_signal_sigprocmask);
POSIX_CASE("signal_sigprocmask_bad_how", case_signal_sigprocmask_bad_how);
POSIX_CASE("signal_set_operations", case_signal_set_operations);
POSIX_CASE("signal_handler_runs", case_signal_handler_runs);
POSIX_CASE("signal_blocked_stays_pending", case_signal_blocked_stays_pending);
POSIX_CASE("signal_sigpending_empty", case_signal_sigpending_empty);
POSIX_CASE("signal_kill_self", case_signal_kill_self);
POSIX_CASE("signal_kill_bad_signum", case_signal_kill_bad_signum);

/*
 * A pointer the caller cannot legally pass is reported, not dereferenced.
 *
 * The kernel copies `struct sigaction` and `sigset_t` through its
 * user-pointer layer instead of reading them in place: a user thread's
 * pointer is resolved through its page table, and an address in the null page
 * is refused outright. Without that, `sigaction(sig, (void *)8, NULL)` would
 * fault in supervisor context.
 */
static int case_signal_sigaction_bad_pointer(void) {
  struct sigaction act;
  struct sigaction out;

  memset(&act, 0, sizeof(act));
  act.sa_handler = test_handler;

  POSIX_ASSERT_ERRNO(sigaction(SIGUSR1, (const struct sigaction *)8, NULL),
                     EFAULT);
  POSIX_ASSERT_ERRNO(sigaction(SIGUSR1, &act, (struct sigaction *)8), EFAULT);

  /* A null `act` stays legal: it means "report the disposition". */
  POSIX_ASSERT_EQ(sigaction(SIGUSR1, NULL, &out), 0);

  return POSIX_PASS;
}

/*
 * `NSIG` is the number of signals, not a signal.
 *
 * newlib defines `NSIG` as 32 for "signal 0 implied", so the last usable
 * number is 31 and 32 has to be rejected - otherwise the disposition table
 * would be indexed one past its end.
 */
static int case_signal_sigaction_rejects_nsig(void) {
  struct sigaction act;

  memset(&act, 0, sizeof(act));
  act.sa_handler = test_handler;

  POSIX_ASSERT_ERRNO(sigaction(NSIG, &act, NULL), EINVAL);

  /* The highest number newlib defines is one below it, and it still works. */
  POSIX_ASSERT_EQ(sigaction(NSIG - 1, &act, NULL), 0);

  act.sa_handler = SIG_DFL;
  POSIX_ASSERT_EQ(sigaction(NSIG - 1, &act, NULL), 0);

  return POSIX_PASS;
}

/* The `sigset_t` bit a signal occupies, read out of the C object. */
static unsigned long mask_value(const sigset_t *set) {
  unsigned long value = 0;
  memcpy(&value, set, sizeof(value));
  return value;
}

/*
 * The C library's `sigaddset()` function and newlib's `sigaddset()` macro must
 * agree on the bit, because a `sigset_t` reaches the kernel unchanged.
 *
 * newlib numbers `SIGUSR1` 30 and spells the macro `1 << (sig)`; the library
 * function used to shift by `sig - 1`, so a set built through one path masked
 * a different signal than the same set built through the other.
 */
static int case_signal_set_bit_matches_macro(void) {
  sigset_t via_macro;
  sigset_t via_function;

  sigemptyset(&via_macro);
  sigemptyset(&via_function);
  sigaddset(&via_macro, SIGUSR1);
  POSIX_ASSERT_EQ(librs_sigaddset_check(&via_function, SIGUSR1), 0);
  POSIX_ASSERT_EQ(mask_value(&via_macro), mask_value(&via_function));

  /* And both agree with the signal number itself. */
  POSIX_ASSERT_EQ(mask_value(&via_macro), 1UL << SIGUSR1);

  POSIX_ASSERT_EQ(sigismember(&via_function, SIGUSR1), 1);
  POSIX_ASSERT_EQ(sigismember(&via_function, SIGUSR2), 0);

  POSIX_ASSERT_EQ(sigdelset(&via_macro, SIGUSR1), 0);
  POSIX_ASSERT_EQ(mask_value(&via_macro), 0);

  return POSIX_PASS;
}

/*
 * Blocking one signal must not block its neighbour.
 *
 * `SIGUSR1` and `SIGUSR2` are the two highest numbers newlib defines (30 and
 * 31), so an off-by-one in either the mask or the pending bitmap shows up here
 * as the wrong signal being held back.
 */
static int case_signal_mask_is_per_signal(void) {
  struct sigaction act;
  sigset_t set;

  memset(&act, 0, sizeof(act));
  act.sa_handler = test_handler;

  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &act, NULL), 0);
  POSIX_ASSERT_EQ(sigaction(SIGUSR2, &act, NULL), 0);

  handler_ran = 0;
  handler_signum = 0;

  sigemptyset(&set);
  sigaddset(&set, SIGUSR1);
  POSIX_ASSERT_EQ(sigprocmask(SIG_BLOCK, &set, NULL), 0);

  /* Blocked: stays pending, no handler. */
  POSIX_ASSERT_EQ(raise(SIGUSR1), 0);
  POSIX_ASSERT_EQ(handler_ran, 0);

  /* Not blocked: delivered, even while the neighbour is held back. */
  POSIX_ASSERT_EQ(raise(SIGUSR2), 0);
  POSIX_ASSERT_EQ(handler_ran, 1);
  POSIX_ASSERT_EQ(handler_signum, SIGUSR2);

  /* Unblocking hands over the held signal. */
  handler_ran = 0;
  POSIX_ASSERT_EQ(sigprocmask(SIG_UNBLOCK, &set, NULL), 0);
  POSIX_ASSERT_EQ(handler_ran, 1);
  POSIX_ASSERT_EQ(handler_signum, SIGUSR1);

  act.sa_handler = SIG_DFL;
  POSIX_ASSERT_EQ(sigaction(SIGUSR1, &act, NULL), 0);
  POSIX_ASSERT_EQ(sigaction(SIGUSR2, &act, NULL), 0);

  return POSIX_PASS;
}

/* Milliseconds between two CLOCK_MONOTONIC readings. */
static long elapsed_ms(const struct timespec *after,
                       const struct timespec *before) {
  return (after->tv_sec - before->tv_sec) * 1000L +
         (after->tv_nsec - before->tv_nsec) / 1000000L;
}

/*
 * `sigtimedwait()` treats its timeout as a relative interval and reports an
 * expired timeout as `EAGAIN`.
 *
 * The kernel used to add up `tv_sec * 1e9 + tv_nsec` and compare it against
 * the current time, which reads a 100 ms interval as "100 ms after the epoch"
 * and returns immediately.
 */
static int case_signal_sigtimedwait_times_out(void) {
  sigset_t set;
  struct timespec timeout;
  struct timespec before;
  struct timespec after;
  long waited;

  sigemptyset(&set);
  sigaddset(&set, SIGUSR1);

  timeout.tv_sec = 0;
  timeout.tv_nsec = 100L * 1000 * 1000;

  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &before), 0);
  POSIX_ASSERT_ERRNO(sigtimedwait(&set, NULL, &timeout), EAGAIN);
  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &after), 0);

  waited = elapsed_ms(&after, &before);
  posix_sayf("  waited ms ", waited);
  /*
   * 100 ms. The window is wider than the 20 ms the interval asks for: the
   * scheduler runs at 100 ticks a second, so a wake-up can land a tick or two
   * late, and this runs under emulation with 32 harts. The value is printed
   * so a drift is visible even when the case passes.
   */
  POSIX_ASSERT(waited >= 80 && waited <= 250);

  return POSIX_PASS;
}

/*
 * A zero timeout polls: the pending set is checked once and the call returns
 * `EAGAIN` without sleeping.
 */
static int case_signal_sigtimedwait_zero_timeout(void) {
  sigset_t set;
  struct timespec timeout;
  struct timespec before;
  struct timespec after;

  sigemptyset(&set);
  sigaddset(&set, SIGUSR1);
  timeout.tv_sec = 0;
  timeout.tv_nsec = 0;

  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &before), 0);
  POSIX_ASSERT_ERRNO(sigtimedwait(&set, NULL, &timeout), EAGAIN);
  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &after), 0);

  POSIX_ASSERT(elapsed_ms(&after, &before) < 20);

  return POSIX_PASS;
}

/* Raised by the helper thread once the main thread is asleep. */
static void *raise_usr2_later(void *argument) {
  sigset_t set;
  struct timespec nap;
  (void)argument;

  /*
   * `kill(0, ...)` is a process-directed signal: it is posted to every
   * thread, and each thread that has it unblocked acts on it. The main
   * thread blocks `SIGUSR2` and collects it with `sigwaitinfo()`, so this
   * thread has to block it as well - otherwise it takes its own signal, and
   * the default disposition of `SIGUSR2` is to terminate, which would retire
   * this thread before its routine returns and leave `pthread_join()`
   * waiting for a barrier nobody reaches.
   */
  sigemptyset(&set);
  sigaddset(&set, SIGUSR2);
  /* The mask is per thread in this kernel, so `sigprocmask()` on the helper
   * blocks it for the helper only. (`pthread_sigmask()` would be the
   * portable spelling, but librs does not export it yet.) */
  sigprocmask(SIG_BLOCK, &set, NULL);

  nap.tv_sec = 0;
  nap.tv_nsec = 50L * 1000 * 1000;
  nanosleep(&nap, NULL);
  kill(0, SIGUSR2);
  return NULL;
}

/*
 * `sigwaitinfo()` is `sigtimedwait()` with an infinite timeout: a null
 * `timeout` means "wait", not "invalid argument". The `siginfo_t` reports the
 * signal that was consumed.
 */
static int case_signal_sigwaitinfo_waits(void) {
  sigset_t set;
  siginfo_t info;
  pthread_t thread;
  struct timespec before;
  struct timespec after;
  int signum;

  sigemptyset(&set);
  sigaddset(&set, SIGUSR2);

  /* `sigwait()` consumes a signal, so it has to be blocked while waiting. */
  POSIX_ASSERT_EQ(sigprocmask(SIG_BLOCK, &set, NULL), 0);

  memset(&info, 0, sizeof(info));

  /* Timed from before the helper starts, so the 50 ms nap is inside the
   * window no matter how long the thread takes to get going. */
  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &before), 0);
  POSIX_ASSERT_EQ(pthread_create(&thread, NULL, raise_usr2_later, NULL), 0);
  signum = sigwaitinfo(&set, &info);
  POSIX_ASSERT_EQ(clock_gettime(CLOCK_MONOTONIC, &after), 0);
  POSIX_ASSERT_EQ(signum, SIGUSR2);

  /* It waited for the helper instead of returning `EINVAL` at once. The
   * helper sleeps 50 ms; a tick boundary can cut that short, so the check is
   * that the call did not return straight away. */
  posix_sayf("  waited ms ", elapsed_ms(&after, &before));
  POSIX_ASSERT(elapsed_ms(&after, &before) >= 20);

  POSIX_ASSERT_EQ(info.si_signo, SIGUSR2);
  POSIX_ASSERT_EQ(info.si_code, SI_USER);

  POSIX_ASSERT_EQ(pthread_join(thread, NULL), 0);
  POSIX_ASSERT_EQ(sigprocmask(SIG_UNBLOCK, &set, NULL), 0);

  return POSIX_PASS;
}

POSIX_CASE("signal_sigaction_bad_pointer", case_signal_sigaction_bad_pointer);
POSIX_CASE("signal_sigaction_rejects_nsig", case_signal_sigaction_rejects_nsig);
POSIX_CASE("signal_set_bit_matches_macro", case_signal_set_bit_matches_macro);
POSIX_CASE("signal_mask_is_per_signal", case_signal_mask_is_per_signal);
POSIX_CASE("signal_sigtimedwait_times_out", case_signal_sigtimedwait_times_out);
POSIX_CASE("signal_sigtimedwait_zero_timeout",
           case_signal_sigtimedwait_zero_timeout);
POSIX_CASE("signal_sigwaitinfo_waits", case_signal_sigwaitinfo_waits);

/*
 * The default disposition of a fatal signal is to terminate, and the kernel
 * used to implement that for `SIGTERM` alone - every other signal whose
 * disposition was `SIG_DFL` was silently discarded.
 *
 * The worker records that it ran, raises `SIGINT` and then records that it
 * survived. Both halves matter: the first rules out "the thread never got
 * scheduled", the second is the behaviour under test.
 */
static volatile int g_worker_started;
static volatile int g_worker_survived;

static void *raise_int_and_report(void *argument) {
  (void)argument;
  g_worker_started = 1;
  raise(SIGINT);
  g_worker_survived = 1;
  return NULL;
}

static int case_signal_default_int_terminates(void) {
  pthread_t thread;
  struct timespec nap;

  g_worker_started = 0;
  g_worker_survived = 0;

  POSIX_ASSERT_EQ(pthread_create(&thread, NULL, raise_int_and_report, NULL), 0);

  /* Long enough for the worker to run, raise, and be retired. */
  nap.tv_sec = 0;
  nap.tv_nsec = 200L * 1000 * 1000;
  nanosleep(&nap, NULL);

  POSIX_ASSERT_EQ(g_worker_started, 1);
  POSIX_ASSERT_EQ(g_worker_survived, 0);

  /* The rest of the image is unharmed: this thread is still running. */
  POSIX_ASSERT_EQ(raise(SIGWINCH), 0);

  return POSIX_PASS;
}

/*
 * The other half of the table: the notification signals and the job-control
 * signals have no default action, so raising them neither kills the thread
 * nor reports an error.
 *
 * A number typo here is what makes the numbering worth pinning: newlib puts
 * `SIGCHLD` at 20 and `SIGCONT` at 19, while Linux puts them at 17 and 18. A
 * table written with Linux's numbers would terminate this thread on
 * `SIGCHLD`.
 */
static int case_signal_default_ignored(void) {
  static const int ignored[] = { SIGCHLD, SIGCONT, SIGURG, SIGWINCH };
  size_t i;

  for (i = 0; i < sizeof(ignored) / sizeof(ignored[0]); i++) {
    posix_sayf("  raise ", ignored[i]);
    POSIX_ASSERT_EQ(raise(ignored[i]), 0);
  }

  return POSIX_PASS;
}

POSIX_CASE("signal_default_int_terminates", case_signal_default_int_terminates);
POSIX_CASE("signal_default_ignored", case_signal_default_ignored);
