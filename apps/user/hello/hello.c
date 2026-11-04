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
 * The first user-mode program BlueKernel runs.
 *
 * Its job is not to be useful, it is to be *evidence*: reaching the `ecall`
 * below means the ELF loader mapped a segment at its link address, the
 * trap-to-user transition installed a stack and dropped privilege, and an
 * `ecall` from U-mode came back to the kernel through the trap frame instead
 * of through the syscall stub the kernel itself uses. The exit status 7 is
 * the assertion the kernel checks in `waitpid`.
 *
 * Freestanding on purpose: no libc, no crt0, no stack protector. A dependency
 * here would be a dependency on a user-space runtime that does not exist yet,
 * and a failure would point at the runtime rather than at the kernel.
 */

#include "nr.h"

typedef unsigned long u64;

/* Three arguments is all `write` and `exit_group` need, and a register-pinned
 * wrapper is the only way to say "put these in a0..a2, the number in a7" in C.
 * The `+r` on a0 is load-bearing: the kernel writes the result there. */
static long syscall3(long nr, long a0, long a1, long a2) {
    register long r0 asm("a0") = a0;
    register long r1 asm("a1") = a1;
    register long r2 asm("a2") = a2;
    register long r7 asm("a7") = nr;
    asm volatile("ecall" : "+r"(r0) : "r"(r7), "r"(r1), "r"(r2) : "memory");
    return r0;
}

/* Exit status the kernel's smoke check expects. Kept in one place so the two
 * sides cannot disagree silently. */
#define EXIT_CODE 7

void _start(void) {
    static const char msg[] = "hello from user mode\n";
    /* `sizeof - 1` drops the terminator: `write` counts bytes, and sending it
     * would put a NUL in the log. */
    syscall3(__NR_write, 1, (long)msg, (long)(sizeof(msg) - 1));
    syscall3(__NR_exit_group, EXIT_CODE, 0, 0);
    /* `exit_group` does not return. If it ever did, falling off the end would
     * run whatever bytes follow — spin instead, so the failure is a hang
     * rather than a wild jump. */
    for (;;) {
    }
}
