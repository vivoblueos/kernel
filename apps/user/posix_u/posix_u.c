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
 * The U-mode counterpart of the POSIX harness (DF-17).
 *
 * The cases under `librs/tests/posix` run as M-mode kernel threads. In that
 * context `in_user_space()` is false and `vfs::uptr` dereferences the pointer
 * as a kernel address, so the two semantics that matter most - "a user pointer
 * must be validated against the caller's page table" and "an invalid pointer
 * is EFAULT from the fault path" - are never exercised. `sigaction()` could
 * only be shown to reject 0x8 because the null page happens to be unmapped.
 *
 * This program runs in U-mode as a real process and asks the same questions
 * through raw `ecall`s:
 *
 *   * a pointer outside every mapped region must come back as EFAULT, not as
 *     a kernel read of that address,
 *   * a valid `sigaction()` followed by `raise()` must run the handler in
 *     U-mode and return through the trampoline's `sigreturn`,
 *   * the fd calls behind `issue8_fdops.c` must report EBADF the way POSIX
 *     says,
 *   * `create_thread()` must start a *thread of this process* in U-mode, not
 *     run the caller's entry point in M-mode, and a thread entry that returns
 *     must retire that thread through the exit trampoline rather than fault at
 *     address zero.
 *
 * Freestanding on purpose, like hello.c and proc.c: no libc, no crt0. The
 * syscall numbers come from `nr.h`, generated from the kernel's own NR enum.
 * The exit status is the failure count, so 0 means every assertion held.
 */

#include "nr.h"

#define EFAULT 14
#define EBADF 9
#define EINVAL 22
/* This kernel's errno numbering is its C library's, not Linux's: the newlib
 * compatible `<errno.h>` puts `ENOSYS` at 88. */
#define ENOSYS 88

#define SIGUSR1 30
#define SIG_BLOCK 0

/* Anonymous private read/write mapping. Values match `user::sys_mmap`. */
#define MAP_PRIVATE 0x02
#define MAP_ANONYMOUS 0x20
#define PROT_READ 0x1
#define PROT_WRITE 0x2

/*
 * A hole in the user address space: the image ends below 0x3f_0000, the stack
 * ends at 0x40_0000 (the trampoline sits at 0x40_1000), and `mmap` starts at
 * 0x80_0000. 0x50_0000 is inside Sv39 and inside no region - exactly what an
 * out-of-bounds caller pointer looks like.
 */
#define BAD_PTR ((void *)0x00500000UL)

static long syscall0(long nr) {
    register long r0 asm("a0");
    register long r7 asm("a7") = nr;
    asm volatile("ecall" : "=r"(r0) : "r"(r7) : "memory");
    return r0;
}

static long syscall1(long nr, long a0) {
    register long r0 asm("a0") = a0;
    register long r7 asm("a7") = nr;
    asm volatile("ecall" : "+r"(r0) : "r"(r7) : "memory");
    return r0;
}

static long syscall3(long nr, long a0, long a1, long a2) {
    register long r0 asm("a0") = a0;
    register long r1 asm("a1") = a1;
    register long r2 asm("a2") = a2;
    register long r7 asm("a7") = nr;
    asm volatile("ecall" : "+r"(r0) : "r"(r7), "r"(r1), "r"(r2) : "memory");
    return r0;
}

static long syscall6(long nr, long a0, long a1, long a2, long a3, long a4,
                     long a5) {
    register long r0 asm("a0") = a0;
    register long r1 asm("a1") = a1;
    register long r2 asm("a2") = a2;
    register long r3 asm("a3") = a3;
    register long r4 asm("a4") = a4;
    register long r5 asm("a5") = a5;
    register long r7 asm("a7") = nr;
    asm volatile("ecall" : "+r"(r0) : "r"(r7), "r"(r1), "r"(r2), "r"(r3),
                 "r"(r4), "r"(r5) : "memory");
    return r0;
}

static int buf_eq(const char *a, const char *b, unsigned long n) {
    for (unsigned long i = 0; i < n; i++) {
        if (a[i] != b[i]) {
            return 0;
        }
    }
    return 1;
}

static unsigned long str_len(const char *s) {
    unsigned long n = 0;
    while (s[n] != '\0') {
        n++;
    }
    return n;
}

static void emit(const char *s) {
    syscall3(__NR_write, 1, (long)s, (long)str_len(s));
}

/*
 * One `write` per line: the console is shared with the kernel's own log lines
 * and the other smoke programs, and splitting a marker across several syscalls
 * gives those writers room to land in the middle of it.
 */
static void append(char *dst, unsigned long *at, const char *src) {
    while (*src != '\0') {
        dst[*at] = *src;
        *at += 1;
        src++;
    }
}

static int failures;

static void check(const char *name, int ok) {
    char line[96];
    unsigned long at = 0;
    append(line, &at, ok ? "POSIX-U-PASS " : "POSIX-U-FAIL ");
    append(line, &at, name);
    line[at++] = '\n';
    syscall3(__NR_write, 1, (long)line, (long)at);
    if (!ok) {
        failures++;
    }
}

/* newlib spells `struct sigaction` as { handler, unsigned long mask, int
 * flags } - the layout the kernel reads (see proc.c). */
typedef struct {
    void (*sa_handler)(int);
    unsigned long sa_mask;
    int sa_flags;
} sigaction_t;

static long u_sigaction(int signo, const sigaction_t *act) {
    return syscall3(__NR_rt_sig_action, signo, (long)act, 0);
}

/* `struct timeval` in the kernel's ABI: two longs on LP64. */
typedef struct {
    long tv_sec;
    long tv_usec;
} timeval_t;

/* An async handler that *returns*: the trampoline's `sigreturn` has to put the
 * interrupted syscall back together, so a flag is the evidence that control
 * came back to U-mode instead of looping inside the kernel. */
static volatile int g_usr1_caught;

static void usr1_handler(int signo) {
    (void)signo;
    g_usr1_caught = 1;
}

/*
 * `create_thread()` from U-mode.
 *
 * The kernel builds a thread of *this* process, so it shares the address space
 * and the descriptor table, but it starts in U-mode at the entry the caller
 * names. The `spawn_hook` and `cleanup` slots of `SpawnArgs` are user function
 * pointers; the kernel must not call them in M-mode, so they stay NULL here and
 * nothing depends on them.
 */
typedef struct {
    void *spawn_hook;
    unsigned char *stack_start;
    unsigned long stack_size;
    void (*entry)(void *);
    void *arg;
    void *cleanup;
} spawn_args_t;

static long u_create_thread(spawn_args_t *args) {
    return syscall1(__NR_create_thread, (long)args);
}

/*
 * Two 16 KiB stacks, one per thread. A static array lands in the writable load
 * segment, which is what the kernel's stack check looks for.
 */
static unsigned char g_stack_return[16384] __attribute__((aligned(16)));
static unsigned char g_stack_exit[16384] __attribute__((aligned(16)));

#define THREAD_MARKER 0x5eed1234UL

static volatile int g_return_ran;
static volatile int g_return_pid;
static volatile int g_return_arg_ok;
static volatile int g_return_io_ok;
static volatile int g_exit_ran;

/*
 * A thread entry that *returns*: the kernel points its `ra` at the read-only
 * exit trampoline, so the return lands on an `exit_thread` ecall instead of on
 * address zero. The process staying alive long enough to print
 * `POSIX-U-DONE` is the evidence that this path did not fault.
 */
static void thread_returns(void *arg) {
    g_return_arg_ok = ((unsigned long)arg == THREAD_MARKER);
    g_return_pid = (int)syscall0(__NR_get_pid);
    /* Writing to fd 1 proves the new thread got the process's descriptor
     * table, not a fresh empty one (which would make this EBADF). */
    g_return_io_ok =
        syscall3(__NR_write, 1, (long)"POSIX-U-THREAD\n", 15) == 15;
    g_return_ran = 1;
}

/* A thread that exits explicitly through the syscall rather than by returning. */
static void thread_exits(void *arg) {
    (void)arg;
    g_exit_ran = 1;
    syscall0(__NR_exit_thread);
    /* `exit_thread` never returns; this is a tombstone if it somehow does. */
    for (;;) {
    }
}

/* Give the scheduler time to run the newly queued threads to completion. */
static void wait_for(volatile int *flag) {
    for (int i = 0; i < 200000 && *flag == 0; i++) {
        syscall0(__NR_sched_yield);
    }
}

void _start(void) {
    long r;

    /* ---- user pointers are validated, and an unmapped one is EFAULT ----
     * Each of these reaches `vfs::uptr` from a process with an address space,
     * so the path taken is the page-table walk, not a raw dereference. */
    r = syscall3(__NR_write, 1, (long)BAD_PTR, 16);
    check("write_bad_pointer_is_efault", r == -EFAULT);

    r = u_sigaction(SIGUSR1, (const sigaction_t *)BAD_PTR);
    check("sigaction_bad_pointer_is_efault", r == -EFAULT);

    r = syscall3(__NR_rt_sig_procmask, SIG_BLOCK, (long)BAD_PTR, 0);
    check("sigprocmask_bad_pointer_is_efault", r == -EFAULT);

    /* `stat` is the out-pointer direction: the lookup succeeds first, then the
     * result has to be copied back through uaccess. */
    r = syscall3(__NR_stat, (long)"/", (long)BAD_PTR, 0);
    check("stat_bad_pointer_is_efault", r == -EFAULT);

    /* ---- a signal handler installed and raised in U-mode ----
     * This is the `issue8_signal.c` path, minus the newlib wrapper: the
     * disposition has to be read from user memory, the handler has to run in
     * U-mode, and `sigreturn` has to resume the interrupted `raise`. */
    sigaction_t sa;
    sa.sa_handler = usr1_handler;
    sa.sa_mask = 0;
    sa.sa_flags = 0;
    r = u_sigaction(SIGUSR1, &sa);
    if (r != 0) {
        check("sigaction_installs_handler", 0);
    } else {
        check("sigaction_installs_handler", 1);
        syscall1(__NR_raise, SIGUSR1);
        check("raise_runs_handler_in_user_mode", g_usr1_caught == 1);
    }

    /* ---- fd semantics behind issue8_fdops.c ---- */
    r = syscall1(__NR_close, 99);
    check("close_unknown_fd_is_ebadf", r == -EBADF);

    long fd = syscall3(__NR_open, (long)"/", 0 /* O_RDONLY */, 0);
    if (fd < 0) {
        check("open_root_directory", 0);
    } else {
        check("open_root_directory", 1);
        check("close_open_fd", syscall1(__NR_close, fd) == 0);
        /* The fd slot is gone after the first close; a second one must not look
         * like success. */
        check("close_twice_is_ebadf", syscall1(__NR_close, fd) == -EBADF);
    }

    r = syscall3(__NR_get_dents, -1, (long)BAD_PTR, 16);
    check("getdents_bad_fd_is_ebadf", r == -EBADF);

    /* ---- create_thread from U-mode ----
     * `SpawnArgs`, `entry` and the stack are all user memory, so the kernel has
     * to read the descriptor through the caller's page table and start the new
     * thread in U-mode rather than running the caller's entry in M-mode. */
    r = u_create_thread((spawn_args_t *)BAD_PTR);
    check("create_thread_bad_args_is_efault", r == -EFAULT);

    spawn_args_t targs;
    targs.spawn_hook = 0;
    targs.cleanup = 0;
    targs.entry = thread_returns;
    targs.arg = (void *)THREAD_MARKER;

    targs.stack_start = g_stack_return;
    targs.stack_size = 0;
    check("create_thread_zero_stack_is_einval", u_create_thread(&targs) == -EINVAL);

    /* The stack pointer is the *top*, so an unaligned size moves it off the
     * 16-byte boundary the image ABI requires. */
    targs.stack_size = sizeof(g_stack_return) + 8;
    check("create_thread_misaligned_stack_is_einval",
          u_create_thread(&targs) == -EINVAL);

    targs.stack_start = (unsigned char *)BAD_PTR;
    targs.stack_size = 4096;
    check("create_thread_unmapped_stack_is_efault",
          u_create_thread(&targs) == -EFAULT);

    targs.stack_start = g_stack_return;
    targs.stack_size = sizeof(g_stack_return);
    targs.entry = 0;
    check("create_thread_null_entry_is_einval", u_create_thread(&targs) == -EINVAL);

    targs.entry = thread_returns;
    r = u_create_thread(&targs);
    if (r <= 0) {
        check("create_thread_creates_a_thread", 0);
    } else {
        check("create_thread_creates_a_thread", 1);
        wait_for(&g_return_ran);
        check("thread_runs_entry", g_return_ran == 1);
        /* Same pid, same descriptor table, same memory: a thread of this
         * process, not a child process. */
        check("thread_shares_the_process",
              g_return_pid == (int)syscall0(__NR_get_pid));
        check("thread_receives_its_argument", g_return_arg_ok == 1);
        check("thread_shares_the_descriptor_table", g_return_io_ok == 1);
    }

    /* ---- a thread can retire itself without taking the process with it ----
     * `exit_thread` is what returning from an entry lands on through the
     * trampoline; calling it directly isolates that syscall from the
     * trampoline's own correctness. */
    targs.stack_start = g_stack_exit;
    targs.stack_size = sizeof(g_stack_exit);
    targs.entry = thread_exits;
    targs.arg = 0;
    r = u_create_thread(&targs);
    if (r <= 0) {
        check("create_thread_second_thread", 0);
    } else {
        check("create_thread_second_thread", 1);
        wait_for(&g_exit_ran);
        check("thread_exit_thread_retires", g_exit_ran == 1);
    }

    /* `thread_returns` has already returned by now; give the exit trampoline
     * time to run before the process exits, so a broken `ra` shows up as a
     * missing `POSIX-U-DONE` rather than as a lucky race. */
    for (int i = 0; i < 10000; i++) {
        syscall0(__NR_sched_yield);
    }

    /* ---- ioctl: the `termios` pointer is a user pointer like any other ----
     * `TCGETS` makes the console driver write `struct termios` into the
     * caller's buffer. An unmapped pointer must be `EFAULT`; collapsing the
     * `uptr` error to a generic bad-argument made `tcgetattr()` report
     * `EINVAL` here. */
    r = syscall3(__NR_ioctl, 1, 0x5401 /* TCGETS */, (long)BAD_PTR);
    check("tcgets_bad_pointer_is_efault", r == -EFAULT);

    /* The other direction: `TCSETS` reads the structure the caller named. */
    r = syscall3(__NR_ioctl, 1, 0x5402 /* TCSETS */, (long)BAD_PTR);
    check("tcsets_bad_pointer_is_efault", r == -EFAULT);

    char termios_buf[64];
    for (int i = 0; i < 64; i++) {
        termios_buf[i] = (char)0xaa;
    }
    r = syscall3(__NR_ioctl, 1, 0x5401 /* TCGETS */, (long)termios_buf);
    check("tcgets_writes_through_user_buffer",
          r == 0 && termios_buf[0] != (char)0xaa);

    /* ---- pipe: descriptors and data both cross uaccess ----
     * `pipe()` publishes the two fds with `write_struct`, so a U-mode caller
     * only works if that path resolves the caller's page table. */
    int pfds[2];
    if (syscall3(__NR_pipe, (long)pfds, 0, 0) != 0) {
        check("pipe_creates_two_descriptors", 0);
    } else {
        check("pipe_creates_two_descriptors", 1);
        char msg[4] = {'p', 'i', 'n', 'g'};
        char got[4] = {0, 0, 0, 0};
        check("pipe_write_from_user_buffer",
              syscall3(__NR_write, pfds[1], (long)msg, 4) == 4);
        check("pipe_read_into_user_buffer",
              syscall3(__NR_read, pfds[0], (long)got, 4) == 4 &&
                  buf_eq(msg, got, 4));
        syscall1(__NR_close, pfds[0]);
        syscall1(__NR_close, pfds[1]);
    }

    /* ---- select: the fd_set and the timeout cross uaccess in both
     * directions ---- */
    int sfds[2];
    if (syscall3(__NR_pipe, (long)sfds, 0, 0) != 0 || sfds[0] >= 64) {
        check("select_sees_readable_pipe", 0);
    } else {
        char one = 'x';
        syscall3(__NR_write, sfds[1], (long)&one, 1);
        /* newlib's `fd_set` is 128 bytes; the kernel reads the first word
         * (`FD_SETSIZE` is 64). The extra words must stay zero. */
        unsigned long set[16];
        for (int i = 0; i < 16; i++) {
            set[i] = 0;
        }
        set[sfds[0] / 64] |= 1UL << (sfds[0] % 64);
        timeval_t tv;
        tv.tv_sec = 0;
        tv.tv_usec = 0;
        r = syscall6(__NR_select, sfds[0] + 1, (long)set, 0, 0, (long)&tv, 0);
        check("select_sees_readable_pipe",
              r == 1 && (set[sfds[0] / 64] & (1UL << (sfds[0] % 64))) != 0);
        syscall1(__NR_close, sfds[0]);
        syscall1(__NR_close, sfds[1]);
    }

    /* ---- dup2: both descriptors share one open file description ---- */
    long src = syscall3(__NR_open, (long)"/bin/hello", 0 /* O_RDONLY */, 0);
    if (src < 0) {
        check("dup2_shares_file_offset", 0);
    } else {
        char hdr[4] = {0, 0, 0, 0};
        char next[4] = {0, 0, 0, 0};
        /* First four bytes of an ELF64 image: 0x7f 'E' 'L' 'F'. */
        int first = syscall3(__NR_read, src, (long)hdr, 4) == 4 &&
                    hdr[0] == 0x7f && hdr[1] == 'E' && hdr[2] == 'L' &&
                    hdr[3] == 'F';
        long dup = syscall3(__NR_dup2, src, 20, 0);
        /* The duplicate continues at offset 4 (ELF class = 2). A
         * per-descriptor offset would read the magic again. */
        int second = dup == 20 &&
                     syscall3(__NR_read, 20, (long)next, 4) == 4 &&
                     next[0] == 2;
        check("dup2_shares_file_offset", first && second);
        syscall1(__NR_close, src);
        syscall1(__NR_close, 20);
    }

    /* ---- a fresh `mmap` page is materialised by the copy helper ---- */
    long va = syscall6(__NR_m_map, 0, 4096, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (va < 0) {
        check("uaccess_faults_in_fresh_mmap_page", 0);
    } else {
        int mp[2];
        if (syscall3(__NR_pipe, (long)mp, 0, 0) != 0) {
            check("uaccess_faults_in_fresh_mmap_page", 0);
        } else {
            /* The page has never been touched, so `write` has to go through
             * the demand-paging path in `fault_in_range` rather than a plain
             * copy of an already-mapped page. */
            check("uaccess_faults_in_fresh_mmap_page",
                  syscall3(__NR_write, mp[1], va, 8) == 8);
            syscall1(__NR_close, mp[0]);
            syscall1(__NR_close, mp[1]);
        }
        syscall3(__NR_m_unmap, va, 4096, 0);
    }

    emit("POSIX-U-DONE\n");
    syscall1(__NR_exit_group, failures);
    for (;;) {
    }
}
