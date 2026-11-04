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
 * The runner is plain C so that the cases exercise the C ABI and the newlib
 * headers, not Rust's view of them. It prints progress with write(1, ...)
 * instead of printf: no stdio buffering means a crash mid-run still leaves the
 * last completed case in the serial log.
 */

#include <string.h>
#include <time.h>
#include <unistd.h>

#include "posix_case.h"

/* newlib's fini array references these; -nostartfiles leaves them undefined. */
void _init(void) {}
void _fini(void) {}

/*
 * App entry.
 *
 * The kernel calls every pointer in `.bk_app_array` from a fresh thread. The
 * entry has to live in the image's own object file: putting it in a Rust
 * `staticlib` would not work, because an archive member is only pulled in when
 * it resolves an undefined symbol, and nothing references a private static.
 *
 * __librs_start_main() (librs) is what an app normally gets: it brings up the
 * librs stdio FILEs, registers the calling thread's POSIX TCB and then calls
 * main(). Skipping it leaves pthread_self()/pthread_join() without a TCB for
 * the app thread.
 */
extern void __librs_start_main(void);

/*
 * The U-mode half of the harness (DF-17): a real process that asks the same
 * questions about user pointers, EFAULT and signal delivery. The M-mode cases
 * cannot reach those paths, because `vfs::uptr` treats their pointers as
 * kernel addresses.
 *
 * It is started from here rather than from `boot` on purpose: only this image
 * has a checker that waits for `POSIX-U-DONE`, and its console output must not
 * interleave with the shell smoke's expectations in the other image.
 */
extern void posix_start_u_probe(void);

static void posix_image_entry(void) { __librs_start_main(); }

__attribute__((used, section(".bk_app_array")))
static void (*const bk_app_entry)(void) = posix_image_entry;

extern const struct posix_case __start_posix_cases[];
extern const struct posix_case __stop_posix_cases[];

void posix_say(const char *text) {
  size_t length = 0;
  while (text[length] != '\0') {
    ++length;
  }
  write(1, text, length);
  write(1, "\n", 1);
}

void posix_sayf(const char *prefix, long value) {
  char buffer[64];
  size_t used = 0;
  while (prefix[used] != '\0' && used < sizeof(buffer) - 1) {
    buffer[used] = prefix[used];
    ++used;
  }

  char digits[24];
  size_t count = 0;
  unsigned long magnitude;
  if (value < 0) {
    if (used < sizeof(buffer) - 1) {
      buffer[used++] = '-';
    }
    magnitude = (unsigned long)(-(value + 1)) + 1;
  } else {
    magnitude = (unsigned long)value;
  }
  do {
    digits[count++] = (char)('0' + (magnitude % 10));
    magnitude /= 10;
  } while (magnitude != 0);
  while (count > 0 && used < sizeof(buffer) - 1) {
    buffer[used++] = digits[--count];
  }
  buffer[used] = '\0';
  posix_say(buffer);
}

static void emit(const char *tag, const char *name) {
  char buffer[96];
  size_t used = 0;
  while (*tag != '\0' && used < sizeof(buffer) - 1) {
    buffer[used++] = *tag++;
  }
  if (used < sizeof(buffer) - 1) {
    buffer[used++] = ' ';
  }
  while (*name != '\0' && used < sizeof(buffer) - 1) {
    buffer[used++] = *name++;
  }
  buffer[used] = '\0';
  posix_say(buffer);
}

int posix_runner_main(void) {
  int passed = 0;
  /* The first app starts while the VFS is still bringing mounts up; opening a
   * path before that spins on an uninitialised working directory.
   *
   * nanosleep rather than usleep: POSIX.1-2008 deprecated usleep, and the two
   * newlib headers differ in where they declare it - the AArch64 one puts it
   * in <sys/unistd.h> behind the POSIX feature macros, the RISC-V one in
   * <unistd.h> proper. nanosleep is in <time.h> on both, with the same
   * prototype, so the case files stay identical across boards. */
  {
    struct timespec delay;
    delay.tv_sec = 0;
    delay.tv_nsec = 200 * 1000 * 1000;
    nanosleep(&delay, NULL);
  }
  posix_start_u_probe();
  int failed = 0;
  int skipped = 0;
  int known = 0;
  int stale = 0;

  posix_say("POSIX-RUNNER begin");
  for (const struct posix_case *item = __start_posix_cases;
       item < __stop_posix_cases; ++item) {
    /* Printed before the call: if a case hangs, the last START in the log is
     * the one that did it. */
    emit("POSIX-START", item->name);
    int result = item->run();
    if (result == POSIX_PASS) {
      if (item->known_issue != NULL) {
        /* Registered as a known defect but it no longer reproduces. Count it
         * as a failure so the marker gets deleted; a stale marker would hide
         * the next regression behind "that one always fails". */
        emit("POSIX-XPASS", item->name);
        posix_say(item->known_issue);
        ++stale;
        continue;
      }
      emit("POSIX-PASS", item->name);
      ++passed;
    } else if (result == POSIX_SKIP) {
      emit("POSIX-SKIP", item->name);
      ++skipped;
    } else if (item->known_issue != NULL) {
      emit("POSIX-KNOWN-FAIL", item->name);
      posix_say(item->known_issue);
      ++known;
    } else {
      emit("ASSERT-FAIL", item->name);
      ++failed;
    }
  }

  /*
   * The result is reported as one line per counter, each with its own marker,
   * plus a final line that the checker uses as the end-of-run signal.
   *
   * The checker cannot assert on several values in one pattern, and its
   * ASSERT-SUCC ends the run as soon as it matches. So the counters are
   * counted instead (COUNT: marker == n) and the last line only says "the run
   * finished" - it deliberately carries no numbers, so that a changed count
   * shows up as a count mismatch rather than as a silently different string.
   */
  posix_sayf("POSIX-COUNT passed=", passed);
  posix_sayf("POSIX-COUNT failed=", failed);
  posix_sayf("POSIX-COUNT known-fail=", known);
  posix_sayf("POSIX-COUNT stale-xfail=", stale);
  posix_sayf("POSIX-COUNT skipped=", skipped);

  /* A regression or a stale marker is announced before the end-of-run line,
   * so the checker can reject it even though the run itself completed. */
  if (failed != 0 || stale != 0) {
    posix_say("POSIX-CHECK-FAIL");
  }
  posix_say("POSIX-CHECK-DONE");
  return (failed == 0 && stale == 0) ? 0 : 1;
}

/*
 * __librs_start_main references `main`; the C cases are all reached from
 * posix_runner_main, so `main` is just the thunk that __librs_start_main
 * calls after the librs runtime is up.
 */
int main(void) { return posix_runner_main(); }
