/*
 * Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *       http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * Freestanding user-mode program that exercises the whole process model:
 * fork, getpid, getppid, waitpid, execve and exit_group.
 *
 * It is the evidence for the librs C wrappers (getpid/getppid/waitpid/fork/
 * execve) and the kernel handlers behind them. The POSIX conformance harness
 * runs in M-mode kernel threads, where `current_process()` is None and these
 * calls return EPERM - so they cannot be tested there. This program runs in
 * U-mode as a real process, which is the only context where fork and friends
 * mean anything.
 *
 * There is no libc here on purpose (see hello.c): every syscall is issued with
 * an inline `ecall`, and the numbers come from `nr.h`, which the build script
 * generates from the kernel's own NR enum. The program's exit status is the
 * test result: 0 means every assertion held, non-zero means at least one did
 * not. The kernel's proc smoke check expects exactly 0.
 */

#include "nr.h"

typedef int pid_t;

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

static pid_t proc_getpid(void) { return (pid_t)syscall0(__NR_get_pid); }
static pid_t proc_getppid(void) { return (pid_t)syscall0(__NR_get_ppid); }
static long proc_waitpid(pid_t pid, int *status, int options) {
    return syscall3(__NR_wait_pid, (long)pid, (long)status, (long)options);
}
static long proc_fork(void) { return syscall0(__NR_fork); }
static long proc_execve(const char *path, const char *const *argv,
                        const char *const *envp) {
    return syscall3(__NR_execve, (long)path, (long)argv, (long)envp);
}
static void proc_exit(int code) { syscall1(__NR_exit_group, code); }

/* newlib spells `struct sigaction` as { handler, unsigned long mask, int
 * flags } - 24 bytes, not the Linux layout - and the kernel reads exactly
 * those bytes. */
typedef struct {
    void (*sa_handler)(int);
    unsigned long sa_mask;
    int sa_flags;
} sigaction_t;

static long proc_sigaction(int signo, const sigaction_t *act) {
    return syscall3(__NR_rt_sig_action, signo, (long)act, 0);
}

/* What a recovered synchronous fault looks like: the handler runs in U-mode
 * and leaves with a status the parent can recognise, so a process that was
 * merely killed cannot pass for one that handled the fault. */
#define FAULT_HANDLED_EXIT 33

static void segv_handler(int signo) {
    (void)signo;
    proc_exit(FAULT_HANDLED_EXIT);
}

static void sigill_handler(int signo) {
    (void)signo;
    proc_exit(FAULT_HANDLED_EXIT);
}

/* An async handler that *returns*: the trampoline's `sigreturn` has to put
 * the interrupted syscall back together, which the fault handlers above never
 * exercise because they leave the process. */
static volatile int g_usr1_caught;

static void usr1_handler(int signo) {
    (void)signo;
    g_usr1_caught = 1;
}

static int proc_raise_child(void) {
    long child = proc_fork();
    if (child == 0) {
        sigaction_t sa;
        sa.sa_handler = usr1_handler;
        sa.sa_mask = 0;
        sa.sa_flags = 0;
        if (proc_sigaction(30 /* SIGUSR1 */, &sa) != 0) {
            proc_exit(60);
        }
        syscall1(__NR_raise, 30);
        /* Reaching here means the handler returned through `sigreturn` and
         * the syscall resumed. `a0` is the interrupted value, so the raise
         * result is not checked; the flag is the evidence. */
        proc_exit(g_usr1_caught ? FAULT_HANDLED_EXIT : 61);
    }
    if (child < 0) {
        return 1;
    }
    int status;
    long reaped = proc_waitpid((pid_t)child, &status, 0);
    if (reaped != child) {
        return 1;
    }
    return ((status >> 8) & 0xff) == FAULT_HANDLED_EXIT ? 0 : 1;
}

/* Runs a child that fault the given way. The child can only exit with
 * FAULT_HANDLED_EXIT if the kernel redirected the fault to its handler. */
static int proc_fault_child(void (*handler)(int), int signo, int illegal) {
    long child = proc_fork();
    if (child == 0) {
        sigaction_t sa;
        sa.sa_handler = handler;
        sa.sa_mask = 0;
        sa.sa_flags = 0;
        if (proc_sigaction(signo, &sa) != 0) {
            proc_exit(60); /* sigaction itself failed */
        }
        if (illegal) {
            __asm__ volatile(".word 0x00000000");
        } else {
            *(volatile int *)0 = 1;
        }
        proc_exit(61); /* no fault reached the handler */
    }
    if (child < 0) {
        return 1;
    }
    int status;
    long reaped = proc_waitpid((pid_t)child, &status, 0);
    if (reaped != child) {
        return 1;
    }
    return ((status >> 8) & 0xff) == FAULT_HANDLED_EXIT ? 0 : 1;
}

/* The kernel encodes the exit code in bits 8..16 of the status word, matching
 * POSIX WEXITSTATUS, so a process that exited with 42 is reaped with status
 * 42 << 8. */
#define WEXITSTATUS(s) (((s) >> 8) & 0xff)

/* The child's own checks fold into its exit code: a clean child exits with the
 * expected value (42, or 7 after a successful execve), and any failed child
 * check shifts it so the parent's waitpid assertion catches it. */
#define CHILD_OK 0
#define CHILD_BAD 1

void _start(void) {
    int failures = 0;
    pid_t parent_pid = proc_getpid();
    if (parent_pid == 0) {
        proc_exit(2); /* the root process must have a non-zero pid */
    }

    /* ---- fork: parent gets the child pid, child gets 0, parenting is right ---- */
    long child = proc_fork();
    if (child < 0) {
        proc_exit(3); /* fork itself failed */
    }
    if (child == 0) {
        int bad = CHILD_OK;
        if (proc_getpid() == parent_pid) {
            bad = CHILD_BAD; /* child must have its own pid */
        }
        if (proc_getppid() != parent_pid) {
            bad = CHILD_BAD; /* and its parent must be the forker */
        }
        proc_exit(bad == CHILD_BAD ? 43 : 42);
    }

    int status;
    long reaped = proc_waitpid((pid_t)child, &status, 0);
    if (reaped != child) {
        failures++;
    }
    if (WEXITSTATUS(status) != 42) {
        failures++; /* child must have exited cleanly with 42 */
    }

    /* ---- execve success: child replaces itself with /bin/hello, exits 7 ---- */
    long child2 = proc_fork();
    if (child2 < 0) {
        proc_exit(4);
    }
    if (child2 == 0) {
        /* On success this does not return; /bin/hello writes a line and exits
         * with 7. Reaching the exit below means execve failed, which is the
         * opposite of what we expect. */
        proc_execve("/bin/hello", (const char *const *)0,
                    (const char *const *)0);
        proc_exit(99);
    }

    int status2;
    long reaped2 = proc_waitpid((pid_t)child2, &status2, 0);
    if (reaped2 != child2) {
        failures++;
    }
    if (WEXITSTATUS(status2) != 7) {
        failures++; /* execve must have run hello to completion */
    }

    /* ---- synchronous faults reach a user handler ----
     * The handler runs in U-mode on the faulting thread's own stack; a
     * store to address 0 must arrive as SIGSEGV and an all-zero instruction
     * word as SIGILL. Both handlers exit with FAULT_HANDLED_EXIT. */
    if (proc_fault_child(segv_handler, 11 /* SIGSEGV */, 0) != 0) {
        failures++;
    }
    if (proc_fault_child(sigill_handler, 4 /* SIGILL */, 1) != 0) {
        failures++;
    }

    /* ---- an async signal runs its handler in U-mode and sigreturn works ---- */
    if (proc_raise_child() != 0) {
        failures++;
    }

    proc_exit(failures);
}
