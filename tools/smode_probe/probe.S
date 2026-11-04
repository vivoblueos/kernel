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
 * S-mode feasibility probe for the S-mode migration (roadmap Phase 0-2).
 *
 * Why this exists
 * ---------------
 * The whole migration rests on facts that the kernel source alone cannot
 * prove:
 *
 *   1. QEMU's `virt` board can enter S-mode at all when it is booted with
 *      `-bios none` - the kernel image starts in M-mode with no OpenSBI
 *      underneath it (see build/boards/qemu_riscv64.gni).
 *   2. A trap taken *from* S-mode is routed to the M-mode `mtvec`. That is
 *      the path an SBI call takes: the S-mode kernel issues `ecall`, the
 *      M-mode firmware services it and returns.
 *   3. S-mode can own its trap vector: with `medeleg` set, an exception
 *      taken in S-mode is delivered to `stvec` and resumed with `sret`.
 *      That is what Phase 1 needs - an S-mode kernel that handles its own
 *      traps instead of leaning on M-mode firmware for every one.
 *   4. `satp` is *effective* in S-mode - which is what forces the kernel,
 *      once it moves down from M-mode, to map itself.
 *
 * Phase 1+2 adds three more, none of which is written down anywhere in the
 * tree and all of which change the design if they turn out false:
 *
 *   5. A timer interrupt can reach an S-mode kernel at all. `mideleg`'s
 *      MTIP bit is read-only zero, so MTIP always traps to M-mode; the only
 *      way S-mode sees a timer is for M-mode to set `mip.STIP` and return.
 *      And because `sip.STIP` is read-only in S-mode (no Sstc on this CPU),
 *      the interrupt can only be *acknowledged* in M-mode - inside the SBI
 *      `set_timer` call. That two-way dependency is why Phase 1 and Phase 2
 *      cannot be delivered separately.
 *   6. The satp switch window works: a trap from U-mode arrives with `satp`
 *      still naming the user table, and the S-mode entry's plan is to clear
 *      it immediately. Those first instructions are fetched *through the
 *      user table*, so the kernel has to be reachable there (identity
 *      mapped, U=0) for the clear to ever execute.
 *   7. (Informational) Whether the PLIC's S-mode context can be driven
 *      directly from S-mode, which decides how external interrupts are
 *      wired. A negative answer is reported, not failed.
 *
 * If any of 1-6 is false the migration plan is wrong, and finding that out
 * after rewriting the trap path would be expensive. So this probe answers
 * them first, on the real emulator, with no kernel involved.
 *
 * The probe
 * ---------
 *   M-mode: set `mtvec`, clear `medeleg`/`mideleg` (so S-mode traps reach
 *   the M-mode handler), program one PMP entry, set `stvec` (S-mode traps
 *   may be delegated to it later), then `mret` into S-mode.
 *
 *   S-mode test 1 - the SBI path: issue one `ecall` carrying a fake SBI
 *   request (a7 = extension id, a0 = function id, a1 = argument), and check
 *   both the reply *and* that the registers the call was not supposed to
 *   touch survived it.
 *
 *   M-mode handler: services the `ecall` the way a real SBI handler will -
 *   saving every general-purpose register, returning the result in a0/a1,
 *   and resuming S-mode just after the `ecall`. It also implements one
 *   out-of-band command, "delegate exceptions to S-mode", which flips
 *   `medeleg` so that the *next* `ecall` is handled by the S-mode vector
 *   instead.
 *
 *   S-mode test 2 - the delegated path: once the delegation is on, the
 *   same `ecall` now lands in `stvec`, is handled entirely in S-mode, and
 *   is resumed with `sret`.
 *
 *   The `satp` proof
 *   ----------------
 *   The S-mode code then installs a Sv39 table that identity-maps the image
 *   but deliberately does *not* map the UART. The next instruction
 *   fetch still succeeds - the code is mapped - and the following access to
 *   the UART traps as a page fault. Landing on a page fault rather than an
 *   instruction fault is the proof that `satp` is in force: the fetch was
 *   translated and permitted, the access was translated and refused.
 *
 * Section layout
 * --------------
 * `_start` is alone in `.text.init`, which the linker script places first
 * at 0x80000000: QEMU's `virt` board with `-bios none` jumps to that
 * address and ignores the ELF entry point, so anything else sitting there
 * would be executed instead. Everything else lives in `.text`.
 *
 * Two conventions the rest of the file depends on
 * ------------------------------------------------
 *   Calling convention: the console helpers call `putc`, so they must save
 *   `ra` across that call - otherwise `ret` returns into the middle of the
 *   helper and the caller never regains control.
 *
 *   Register save area: the M-mode handler saves the interrupted S-mode
 *   registers into a static area (`m_saved`) rather than onto a stack,
 *   because it has to switch to the M-mode stack first and still be able
 *   to find the area afterwards. Reaching the area needs a pointer
 *   register, and t0/t1 - the first two registers a handler would clobber -
 *   are saved through a 16-byte stack slot first.
 *
 *   The two privilege levels never share a stack: the M-mode handler runs
 *   on `m_stack`, the S-mode code on `s_stack`, and `mret` does not restore
 *   `sp`, so the handler restores the S-mode stack pointer explicitly.
 */

    .option norvc

/* ------------------------------------------------------------------ */
/* M-mode entry - must be the first thing at 0x80000000.              */
/* ------------------------------------------------------------------ */
    .section .text.init, "ax"
    .globl _start
_start:
    la      sp, m_stack_top

    /* Our M-mode trap handler services the S-mode `ecall`. */
    la      t0, m_trap
    csrw    mtvec, t0

    /*
     * The S-mode trap vector. `stvec` is written here, from M-mode, but
     * only becomes reachable once `medeleg` delegates the exceptions to
     * S-mode - which happens later, on request from the S-mode code.
     */
    la      t0, s_trap
    csrw    stvec, t0

    /*
     * No exception delegation yet: an exception taken from S-mode must
     * reach the M-mode `mtvec`. That is exactly the path an SBI call takes,
     * and it is the first thing the migration depends on.
     */
    csrw    medeleg, zero

    /*
     * Delegate the *S-level* interrupts: SSIP(1) / STIP(5) / SEIP(9).
     *
     * The M-level ones - MSIP(3), MTIP(7), MEIP(11) - are read-only zero
     * in `mideleg`: the architecture reserves them for M-mode, so a timer
     * interrupt can never be delegated, only *forwarded* (M-mode takes it
     * and sets `mip.STIP`). Phase 1+2 is built on that, and nothing else in
     * the tree can prove it, so it is measured below.
     *
     * Note the CSR-immediate forms cannot reach these bits: `csrsi` takes a
     * 5-bit uimm, far too small for 0x222.
     */
    li      t0, 0x222
    csrw    mideleg, t0

    /*
     * Enable the machine-level interrupt sources.
     *
     * This is the step the probe originally omitted, and its absence mashes
     * two different enable bits into one mental model: dropping the
     * privilege level below M removes the need for `mstatus.MIE`, but the
     * *per-source* `mie` bits still gate every interrupt. Without MTIE the
     * CLINT compares mtime all it likes and nothing is ever delivered - the
     * kernel's own `bootstrap()` sets exactly these three bits for the same
     * reason.
     */
    li      t0, 0x888                /* MTIE(7) | MSIE(3) | MEIE(11) */
    csrw    mie, t0

    /*
     * Park the timer and the software interrupt before S-mode runs, and
     * drop any S-level pending bit the reset state may have left behind.
     */
    li      t0, 0x222
    csrc    mip, t0
    li      t3, 0x02004000           /* CLINT mtimecmp[0] */
    li      t4, -1
    sd      t4, 0(t3)
    li      t3, 0x02000000           /* CLINT msip[0] */
    sw      zero, 0(t3)

    /*
     * PMP entry 0: NAPOT, low 4 GiB, R|W|X, L=0 - the same policy the
     * kernel programs today (kernel/kernel/src/arch/riscv/pmp.rs). S-mode
     * accesses are permission-checked against it, so it has to be right for
     * S-mode too, not just U-mode.
     */
    li      t0, 0x1fffffff           /* pmpaddr0: base 0, size 4 GiB */
    csrw    pmpaddr0, t0
    li      t0, 0x1f                /* pmpcfg0: A=NAPOT, R, W, X */
    csrw    pmpcfg0, t0

    /* Zero the page tables: the unused entries must be invalid. */
    la      a0, root_pte
    call    zero_4k
    la      a0, l1_pte
    call    zero_4k
    la      a0, leaf_pte
    call    zero_4k

    la      a0, m_banner
    call    puts
    csrr    a0, misa
    call    puthex
    call    putnl

    /*
     * Enter S-mode: `mepc` = S-mode entry, `MPP` = S, `MPIE` = 1 so the
     * S-mode code runs with interrupts enabled and `mret` restores that.
     */
    la      t0, s_entry
    csrw    mepc, t0
    li      t0, 0x1800              /* MPP mask */
    csrc    mstatus, t0
    li      t0, 0x800               /* MPP = S */
    csrs    mstatus, t0
    li      t0, 0x80                /* MPIE */
    csrs    mstatus, t0

    /* `mret` does not restore `sp`, so the S-mode stack is set up here. */
    la      sp, s_stack_top
    mret

/* ------------------------------------------------------------------ */
/* Everything else.                                                    */
/* ------------------------------------------------------------------ */
    .section .text, "ax"

/* a0 = byte */
putc:
    li      t3, 0x10000000          /* QEMU virt NS16550 THR */
    li      t4, 5                   /* LSR: transmitter holding register empty */
1:
    lb      t5, 5(t3)               /* LSR */
    andi    t5, t5, 1 << 5
    beqz    t5, 1b
    sb      a0, 0(t3)
    ret

/*
 * a0 = 64-bit value, printed as hex.
 *
 * `ra` is saved across the `call putc` below - without that, `ret` would
 * jump back into this function instead of to the caller.
 */
puthex:
    addi    sp, sp, -16
    sd      ra, 8(sp)
    mv      t0, a0
    li      t1, 16
1:
    srl     t2, t0, 60
    li      t3, 10
    blt     t2, t3, 2f
    addi    t2, t2, 'a' - 10
    j       3f
2:
    addi    t2, t2, '0'
3:
    mv      a0, t2
    call    putc
    slli    t0, t0, 4
    addi    t1, t1, -1
    bnez    t1, 1b
    ld      ra, 8(sp)
    addi    sp, sp, 16
    ret

/* a0 = NUL-terminated string */
puts:
    addi    sp, sp, -16
    sd      ra, 8(sp)
    mv      t0, a0
1:
    lbu     a0, 0(t0)
    beqz    a0, 2f
    call    putc
    addi    t0, t0, 1
    j       1b
2:
    ld      ra, 8(sp)
    addi    sp, sp, 16
    ret

putnl:
    addi    sp, sp, -16
    sd      ra, 8(sp)
    li      a0, '\n'
    call    putc
    ld      ra, 8(sp)
    addi    sp, sp, 16
    ret

/* a0 = address of 4096 bytes to clear */
zero_4k:
    mv      t0, a0
    li      t1, 512
1:
    sd      zero, 0(t0)
    addi    t0, t0, 8
    addi    t1, t1, -1
    bnez    t1, 1b
    ret

/* ------------------------------------------------------------------ */
/* M-mode trap handler                                                 */
/* ------------------------------------------------------------------ */
m_trap:
    /*
     * The trap came from S-mode, so `sp` is the S-mode stack. Save the
     * interrupted S-mode registers before touching anything else: the
     * handler is about to clobber every register it owns.
     *
     * The save area is static, not on a stack, because the handler has to
     * move to the M-mode stack and still be able to find the area
     * afterwards. Reaching it needs a pointer register, and t0/t1 - the
     * first registers a handler would destroy - are therefore parked on
     * the S-mode stack for the moment it takes to compute the address.
     */
    addi    sp, sp, -16
    sd      t0, 0(sp)
    sd      t1, 8(sp)
    la      t0, m_saved
    ld      t1, 0(sp)
    sd      t1, 8(t0)               /* the interrupted t0 */
    ld      t1, 8(sp)
    sd      t1, 16(t0)              /* the interrupted t1 */
    addi    sp, sp, 16

    sd      ra, 0(t0)
    sd      t2, 24(t0)
    sd      t3, 32(t0)
    sd      t4, 40(t0)
    sd      t5, 48(t0)
    sd      t6, 56(t0)
    sd      a0, 64(t0)
    sd      a1, 72(t0)
    sd      a2, 80(t0)
    sd      a3, 88(t0)
    sd      a4, 96(t0)
    sd      a5, 104(t0)
    sd      a6, 112(t0)
    sd      a7, 120(t0)
    sd      s0, 128(t0)
    sd      s1, 136(t0)
    sd      s2, 144(t0)
    sd      s3, 152(t0)
    sd      s4, 160(t0)
    sd      s5, 168(t0)
    sd      s6, 176(t0)
    sd      s7, 184(t0)
    sd      s8, 192(t0)
    sd      s9, 200(t0)
    sd      s10, 208(t0)
    sd      s11, 216(t0)
    sd      sp, 224(t0)             /* the interrupted (S-mode) stack pointer */

    /* From here on the M-mode handler runs on its own stack. */
    la      sp, m_stack_top

    csrr    t0, mcause

    /*
     * The two machine-level interrupts the migration depends on. Neither
     * can be delegated, so M-mode takes them and re-publishes them at
     * S-level by writing `mip`.
     */
    li      t1, 0x8000000000000007   /* MTIP: machine timer interrupt */
    beq     t0, t1, m_timer_fwd
    li      t1, 0x8000000000000003   /* MSIP: machine software interrupt */
    beq     t0, t1, m_soft_fwd

    li      t1, 9                   /* ecall from S-mode */
    beq     t0, t1, m_ecall
    li      t1, 15                  /* store page fault: the expected end */
    beq     t0, t1, m_page_fault
    li      t1, 13                  /* load page fault: same idea */
    beq     t0, t1, m_page_fault
    li      t1, 1                   /* instruction page fault */
    beq     t0, t1, m_instr_fault

    la      a0, m_unexpected
    call    puts
    csrr    a0, mcause
    call    puthex
    la      a0, m_space
    call    puts
    csrr    a0, mepc
    call    puthex
    la      a0, m_space
    call    puts
    csrr    a0, mtval
    call    puthex
    call    putnl

    /* Dump the page tables: M-mode reads them physically, so this is a
     * direct look at what the S-mode code actually programmed. */
    la      a0, m_root
    call    puts
    la      t0, root_pte
    ld      a0, 16(t0)              /* root[2] */
    call    puthex
    la      a0, m_space
    call    puts
    la      t0, l1_pte
    ld      a0, 0(t0)               /* l1[0] */
    call    puthex
    la      a0, m_space
    call    puts
    la      t0, leaf_pte
    ld      a0, 0(t0)               /* leaf[0] */
    call    puthex
    la      a0, m_space
    call    puts
    la      t0, leaf_pte
    ld      a0, 40(t0)              /* leaf[5] */
    call    puthex
    la      a0, m_space
    call    puts
    csrr    a0, satp
    call    puthex
    call    putnl

    j       exit_fail

/*
 * Service the fake SBI call.
 *
 * The SBI convention: `a7` = extension id, `a0` = function id, `a1..` =
 * arguments; the reply is `a0` = error code plus `a1..` = results. Every
 * register except a0/a1 must survive the call, so the general-purpose
 * registers were saved by `m_trap` and are restored before returning -
 * exactly what a real M-mode firmware handler has to do.
 */
m_ecall:
    la      t0, m_saved
    ld      t1, 120(t0)             /* a7 = extension id */

    /* The real SBI TIME extension: set_timer. This is the operation that
     * has to clear STIP, because S-mode cannot. */
    li      t2, 0x54494d45           /* "TIME" */
    beq     t1, t2, m_cmd_set_timer

    /* Everything else in this probe is an out-of-band control command. */
    li      t2, 0x544d4d
    bne     t1, t2, m_ecall_default

    la      t0, m_saved
    ld      t1, 64(t0)              /* a0 = function id */
    li      t2, 1
    beq     t1, t2, m_cmd_delegate
    li      t2, 3
    beq     t1, t2, m_cmd_undelegate
    li      t2, 4
    beq     t1, t2, m_cmd_delegate_u

m_ecall_default:
    la      a0, m_got_ecall
    call    puts
    la      t0, m_saved
    ld      a0, 120(t0)             /* a7 */
    call    puthex
    la      a0, m_space
    call    puts
    la      t0, m_saved
    ld      a0, 64(t0)              /* a0 */
    call    puthex
    call    putnl

    /* Reply: a0 = 0 (success), a1 = a recognisable result. */
    li      a0, 0
    li      a1, 0x5678
    j       m_ecall_restore

/*
 * Out-of-band command: delegate exceptions to S-mode.
 *
 * `medeleg` is an M-mode CSR, so the S-mode code cannot delegate on its
 * own - it has to ask the M-mode side to do it. Once this returns, the
 * next `ecall` is taken in S-mode and delivered to `stvec` instead of
 * arriving here.
 */
m_cmd_delegate:
    la      a0, m_delegate
    call    puts
    li      t0, 1 << 9              /* delegate "ecall from S-mode" */
    csrw    medeleg, t0
    li      a0, 0
    li      a1, 0x0d15
    j       m_ecall_restore

/*
 * Hand the SBI channel back to M-mode. Test 2 delegated cause 9 to S-mode;
 * before the timer measurement issues a real SBI call, that delegation has
 * to be undone, or the call would land in `s_trap` instead of here.
 */
m_cmd_undelegate:
    csrw    medeleg, zero
    li      a0, 0
    li      a1, 0
    j       m_ecall_restore

/*
 * Delegate "ecall from U-mode" (cause 8) so the U-mode stub's trap is taken
 * by S-mode. Cause 9 stays with M-mode: it is the SBI channel.
 */
m_cmd_delegate_u:
    li      t0, 1 << 8
    csrw    medeleg, t0
    li      a0, 0
    li      a1, 0
    j       m_ecall_restore

/*
 * SBI set_timer, and the reason Phase 1 and Phase 2 cannot be split.
 *
 * An S-mode sip.STIP is read-only (no Sstc extension on this QEMU CPU), so
 * the S-mode timer handler cannot acknowledge its own interrupt. The only
 * place it can be cleared is here, in M-mode, while programming the next
 * deadline. Doing both in one operation is what closes the loop.
 */
m_cmd_set_timer:
    la      t0, m_saved
    ld      t1, 72(t0)              /* a1 = stime_value */
    li      t3, 0x02004000
    sd      t1, 0(t3)               /* CLINT mtimecmp[0] */
    li      t2, 0x20
    csrc    mip, t2                 /* clear STIP - S-mode cannot */
    la      a0, m_set_timer
    call    puts
    li      a0, 0
    li      a1, 0
    j       m_ecall_restore

/*
 * Forward the machine timer interrupt to S-mode.
 *
 * Parking mtimecmp first is not optional: MTIP stays asserted while
 * mtime < mtimecmp, so without it `mret` would immediately re-enter M-mode
 * and S-mode would never get to run. This is the exact deadlock the kernel
 * firmware has to avoid.
 */
m_timer_fwd:
    li      t3, 0x02004000
    li      t4, -1
    sd      t4, 0(t3)
    li      t0, 0x20                /* mip.STIP */
    csrs    mip, t0
    la      a0, m_timer_fwd_msg
    call    puts
    j       m_restore_no_advance

/* Forward the machine software interrupt as mip.SSIP. */
m_soft_fwd:
    li      t3, 0x02000000
    sw      zero, 0(t3)              /* clear the MSIP source */
    li      t0, 0x2                 /* mip.SSIP */
    csrs    mip, t0
    la      a0, m_soft_fwd_msg
    call    puts
    j       m_restore_no_advance

/*
 * Restore the interrupted S-mode context and go back to S-mode.
 *
 * The order matters: the S-mode stack pointer is put back first (nothing
 * below pushes on the stack any more), the return address of the `ecall`
 * is advanced, `MPP` is set back to S, and only then are the registers
 * restored - t0 last, because it is the pointer into the save area.
 */
m_ecall_restore:
    la      t0, m_saved
    ld      sp, 224(t0)             /* the S-mode stack pointer */

    csrr    t0, mepc
    addi    t0, t0, 4               /* resume after the `ecall` */
    csrw    mepc, t0
    j       m_restore_common

/*
 * An interrupt does not advance `mepc`: it already points at the first
 * instruction that has not executed, so resuming there re-runs nothing.
 */
m_restore_no_advance:
    la      t0, m_saved
    ld      sp, 224(t0)
    j       m_restore_common

m_restore_common:
    li      t0, 0x1800
    csrc    mstatus, t0             /* MPP = S */
    li      t0, 0x800
    csrs    mstatus, t0

    la      t0, m_saved
    ld      ra, 0(t0)
    ld      t1, 16(t0)
    ld      t2, 24(t0)
    ld      t3, 32(t0)
    ld      t4, 40(t0)
    ld      t5, 48(t0)
    ld      t6, 56(t0)
    ld      a2, 80(t0)
    ld      a3, 88(t0)
    ld      a4, 96(t0)
    ld      a5, 104(t0)
    ld      a6, 112(t0)
    ld      a7, 120(t0)
    ld      s0, 128(t0)
    ld      s1, 136(t0)
    ld      s2, 144(t0)
    ld      s3, 152(t0)
    ld      s4, 160(t0)
    ld      s5, 168(t0)
    ld      s6, 176(t0)
    ld      s7, 184(t0)
    ld      s8, 192(t0)
    ld      s9, 200(t0)
    ld      s10, 208(t0)
    ld      s11, 216(t0)
    ld      t0, 8(t0)               /* the interrupted t0, restored last */

    /* a0/a1 keep the reply values. */
    mret

/*
 * The expected page fault: the S-mode access to the UART was translated
 * and refused, while the instruction fetch just before it was translated
 * and allowed. That difference is the proof that `satp` is in force in
 * S-mode.
 */
m_page_fault:
    la      a0, m_satp_effective
    call    puts

    /*
     * Continue into the Phase 1+2 measurements.
     *
     * `satp` is dropped first. The `puts` above reached the UART only
     * because M-mode is never translated - S-mode still cannot use the
     * console until translation is off again.
     *
     * `mepc` is *redirected*, not advanced: the faulting instruction is the
     * UART store inside `puts`, and resuming just after it would fault again
     * on the next character.
     */
    csrw    satp, zero
    sfence.vma zero, zero

    /*
     * Take the SBI channel back.
     *
     * Test 2 delegated cause 9 to S-mode, and S-mode cannot write `medeleg`
     * - it is an M-mode CSR - so the delegation can only be undone from
     * here. Left as it was, every later SBI call would loop straight back
     * into `stvec` and never reach the firmware, which is precisely the
     * trap the first run of this probe fell into.
     */
    csrw    medeleg, zero

    la      t0, m_saved
    ld      sp, 224(t0)
    la      t0, s_phase2
    csrw    mepc, t0
    j       m_restore_common

/*
 * An instruction page fault would mean the code page was not mapped, so
 * the fetch failed instead of the access - the proof would be void.
 */
m_instr_fault:
    la      a0, m_instr_fault_msg
    call    puts
    j       exit_fail

/* ------------------------------------------------------------------ */
/* S-mode trap handler (reached through stvec once delegated)        */
/* ------------------------------------------------------------------ */
s_trap:
    /*
     * A trap in S-mode does not switch stacks and does not save the
     * general-purpose registers, so the handler has to preserve the ones
     * the interrupted code cares about itself.
     */
    addi    sp, sp, -48
    sd      ra, 0(sp)
    sd      t0, 8(sp)
    sd      t1, 16(sp)
    sd      t2, 24(sp)
    sd      a1, 32(sp)

    csrr    t3, scause
    li      t2, 9                   /* ecall from S-mode */
    bne     t3, t2, s_trap_unexpected

    la      a0, s_delegated
    call    puts

    /* Answer the delegated call entirely in S-mode. */
    csrr    t3, sepc
    addi    t3, t3, 4
    csrw    sepc, t3
    li      a0, 0x2222

    ld      ra, 0(sp)
    ld      t0, 8(sp)
    ld      t1, 16(sp)
    ld      t2, 24(sp)
    ld      a1, 32(sp)
    addi    sp, sp, 48
    sret

s_trap_unexpected:
    la      a0, s_unexpected
    call    puts
    csrr    a0, scause
    call    puthex
    call    putnl
    ld      ra, 0(sp)
    addi    sp, sp, 48
    j       exit_fail

/* ------------------------------------------------------------------ */
/* S-mode entry                                                        */
/* ------------------------------------------------------------------ */
s_entry:
    la      a0, s_banner
    call    puts
    csrr    a0, sstatus
    call    puthex
    call    putnl

    /*
     * Test 1 - the SBI path: issue a fake SBI call: a7 = TIMER extension
     * id, a0 = function id, a1 = argument. t0 and t1 are loaded with
     * known values first, so the handler's promise that non-a0/a1
     * registers survive the call can be checked afterwards.
     */
    li      t0, 0xdeadbeef
    li      t1, 0x0badf00d
    li      a7, 0x544d4d
    li      a0, 0
    li      a1, 0x1234
    ecall

    /* a0 must be 0 (success), a1 the handler's result, t0/t1 untouched. */
    bnez    a0, s_fail
    li      t2, 0x5678
    bne     a1, t2, s_fail
    li      t2, 0xdeadbeef
    bne     t0, t2, s_fail
    li      t2, 0x0badf00d
    bne     t1, t2, s_fail

    la      a0, s_ecall_ok
    call    puts

    /*
     * Test 2 - the delegated path: ask the M-mode side to delegate
     * exceptions to S-mode, then issue the same `ecall` again. It must now
     * be handled by `stvec` in S-mode and resumed with `sret`.
     */
    li      a7, 0x544d4d
    li      a0, 1
    li      a1, 0
    ecall
    bnez    a0, s_fail

    li      t0, 0xdeadbeef
    li      t1, 0x0badf00d
    li      a7, 0x544d4d
    li      a0, 0
    li      a1, 0x1234
    ecall
    li      t2, 0x2222
    bne     a0, t2, s_fail
    li      t2, 0xdeadbeef
    bne     t0, t2, s_fail
    li      t2, 0x0badf00d
    bne     t1, t2, s_fail
    la      a0, s_deleg_ok
    call    puts

    /*
     * Build the page table: identity-map 2 MiB starting at the image base
     * with U=1, so the S-mode fetch keeps working with `satp` enabled.
     * The UART is deliberately left unmapped.
     */
    la      t0, leaf_pte
    li      t1, 512
    li      t2, 0
    li      t3, 0x80000              /* first physical page number */
1:
    slli    t4, t2, 3
    add     t4, t0, t4
    slli    t5, t3, 10
    /*
     * V|R|W|X|A|D, and U = 0.
     *
     * The U bit is the subtle one, and getting it wrong looks exactly like
     * a broken page table. A PTE with U=1 marks the page as reachable from
     * U-mode; `mstatus.SUM` then decides whether S-mode may touch such a
     * page at all, and with SUM = 0 (the reset value) an S-mode access to a
     * U-mode page faults - *even though the access is being made by S-mode*.
     * The permission check does not know the accessor's intent, only the
     * page's U bit and SUM.
     *
     * So an S-mode kernel mapping its own image must use U = 0 (or set
     * SUM = 1, which would also let it reach U-mode pages - a wider hole
     * than the kernel wants). U = 0 is the correct choice: the kernel's own
     * pages are S-mode pages, and the U-mode pages the kernel manages for
     * user processes live in a different page table entirely.
     *
     * This is a hard constraint of the migration, not an artefact of the
     * probe: it applies to every page the S-mode kernel maps for itself.
     */
    ori     t5, t5, 0xcf             /* V|R|W|X|A|D, U=0 */
    sd      t5, 0(t4)
    addi    t2, t2, 1
    addi    t3, t3, 1
    bne     t1, t2, 1b

    /* root[2] -> l1 table, l1[0] -> leaf table */
    la      t0, root_pte
    la      t1, l1_pte
    srli    t1, t1, 12
    slli    t1, t1, 10
    ori     t1, t1, 0x01             /* pointer to a level-1 table */
    li      t2, 16
    add     t0, t0, t2
    sd      t1, 0(t0)

    la      t0, l1_pte
    la      t1, leaf_pte
    srli    t1, t1, 12
    slli    t1, t1, 10
    ori     t1, t1, 0x01             /* pointer to a leaf table */
    sd      t1, 0(t0)

    /*
     * satp = MODE(8) | root page number.
     *
     * `satp` holds the root table's *physical page number* in bits 43:0 -
     * there is no shift here, the PPN is already a page number. (A PTE is
     * different: its PPN lives in bits 53:10, so a PTE does need a shift.)
     * The mode field is bits 63:60, built with a shift because `ori`
     * cannot take a 64-bit immediate.
     */
    la      t0, root_pte
    srli    t0, t0, 12
    li      t1, 8
    slli    t1, t1, 60
    or      t0, t0, t1
    csrw    satp, t0
    sfence.vma zero, zero

    /*
     * This fetch is translated through the table above: the code page is
     * mapped (with U=0, as S-mode requires), so it succeeds. The access to
     * the UART inside `puts` then hits the unmapped UART and traps - as a
     * page fault.
     */
    la      a0, s_about_to_fault
    call    puts

    /* Not reached: the access above traps. */
    j       s_fail

/* ------------------------------------------------------------------ */
/* S-mode phase 2: the three facts Phase 1+2 rest on.                  */
/* ------------------------------------------------------------------ */
s_phase2:
    /*
     * Test 5 - the timer forward.
     *
     * Hand the SBI channel back to M-mode first: test 2 delegated
     * "ecall from S-mode" to S-mode, and a real SBI call has to reach the
     * firmware instead of looping back into `stvec`.
     */
    li      a7, 0x544d4d
    li      a0, 3
    li      a1, 0
    ecall
    bnez    a0, s_fail

    la      t0, s_trap_stip
    csrw    stvec, t0

    /*
     * Arm the timer. CLINT is inside the PMP window, so S-mode can write
     * mtimecmp directly - exactly the kernel's situation today.
     *
     * mtime/mtimecmp offsets (0xbff8, 0x4000) do not fit a 12-bit
     * immediate, hence the separate address registers.
     */
    li      t3, 0x0200bff8           /* CLINT mtime */
    ld      t1, 0(t3)
    li      t4, 0x20000
    add     t1, t1, t4
    li      t3, 0x02004000           /* CLINT mtimecmp[0] */
    sd      t1, 0(t3)

    li      t0, 0x20                 /* sie.STIE */
    csrs    sie, t0
    li      t0, 0x2                  /* sstatus.SIE */
    csrs    sstatus, t0

    /*
     * Bounded wait: a missing interrupt must report, not hang until the
     * runner's timeout fires.
     */
    li      s0, 1
    slli    s0, s0, 24
    la      s1, timer_done
1:
    lw      t0, 0(s1)
    bnez    t0, 2f
    addi    s0, s0, -1
    beqz    s0, s_timer_timeout
    j       1b
2:
    li      t0, 0x20
    csrc    sie, t0

    /*
     * Test 6 - the satp switch window.
     *
     * A trap from U-mode lands with `satp` still naming the *user* table,
     * so the first instructions of the S-mode entry are fetched through it.
     * The kernel's plan is to clear `satp` immediately; for that to work
     * the entry has to be reachable *before* the clear - which is what this
     * measures.
     */
    li      a7, 0x544d4d
    li      a0, 4                    /* delegate ecall-from-U */
    li      a1, 0
    ecall
    bnez    a0, s_fail

    la      a0, u_root
    call    zero_4k
    la      a0, u_l1u
    call    zero_4k
    la      a0, u_leafu
    call    zero_4k
    la      a0, u_l1k
    call    zero_4k

    /*
     * VA 0x0001_0000 -> the physical page holding `u_stub`, U=1, R|X.
     * One 4 KiB leaf: the page is user-reachable only through that VA.
     */
    la      t0, u_leafu
    la      t1, u_stub
    srli    t1, t1, 12
    slli    t1, t1, 10
    ori     t1, t1, 0xdb             /* V|R|X|A|D|U */
    li      t2, 0x10                 /* VPN[0] of 0x0001_0000 */
    slli    t2, t2, 3
    add     t0, t0, t2
    sd      t1, 0(t0)

    /* root[0] -> u_l1u -> u_leafu (VA 0..2 MiB) */
    la      t0, u_root
    la      t1, u_l1u
    srli    t1, t1, 12
    slli    t1, t1, 10
    ori     t1, t1, 0x01
    sd      t1, 0(t0)
    la      t0, u_l1u
    la      t1, u_leafu
    srli    t1, t1, 12
    slli    t1, t1, 10
    ori     t1, t1, 0x01
    sd      t1, 0(t0)

    /*
     * VA 0x8000_0000 -> PA 0x8000_0000, a 2 MiB leaf with U=0: the kernel
     * window. This one entry is what keeps the S-mode entry fetching.
     */
    la      t0, u_l1k
    li      t1, 0x80000              /* PA 0x8000_0000 as a page number */
    slli    t1, t1, 10
    ori     t1, t1, 0xcf             /* V|R|W|X|A|D, U=0 */
    sd      t1, 0(t0)
    la      t0, u_root
    la      t1, u_l1k
    srli    t1, t1, 12
    slli    t1, t1, 10
    ori     t1, t1, 0x01
    li      t2, 16                   /* root[2] */
    add     t0, t0, t2
    sd      t1, 0(t0)

    la      t0, s_trap_u
    csrw    stvec, t0
    la      t0, s_stack_top
    csrw    sscratch, t0             /* the S-mode stack the entry swaps in */

    /*
     * The stub's *virtual* address, not 0x0001_0000: the leaf maps the
     * whole physical page, and `u_stub` sits at some offset inside it.
     * Using the page base would start U-mode at whatever else shares that
     * page - which for this layout is `_start`, and the first `csrw` there
     * is an illegal instruction in U-mode. Computing the offset keeps the
     * address correct no matter where the linker puts the stub.
     */
    la      t0, u_stub
    srli    t1, t0, 12
    slli    t1, t1, 12
    sub     t1, t0, t1               /* offset within its page */
    li      t0, 0x10000              /* the VA the page is mapped at */
    add     t0, t0, t1
    csrw    sepc, t0
    li      t0, 0x100                /* SPP */
    csrc    sstatus, t0              /* SPP = 0: sret lands in U-mode */
    li      t0, 0x20                 /* SPIE */
    csrs    sstatus, t0

    la      t0, u_root
    srli    t0, t0, 12
    li      t1, 8
    slli    t1, t1, 60
    or      t0, t0, t1
    csrw    satp, t0
    sfence.vma zero, zero

    li      sp, 0x11000              /* a U-mode stack the stub never uses */
    sret

/* ------------------------------------------------------------------ */
/* S-mode timer handler: the STIP end of the forward.                  */
/* ------------------------------------------------------------------ */
s_trap_stip:
    addi    sp, sp, -64
    sd      ra, 0(sp)
    sd      t0, 8(sp)
    sd      t1, 16(sp)
    sd      t2, 24(sp)
    sd      a0, 32(sp)
    sd      a1, 40(sp)
    sd      s0, 48(sp)
    sd      s1, 56(sp)

    csrr    t0, scause
    li      t1, 0x8000000000000005   /* STIP */
    bne     t0, t1, s_stip_unexpected

    /* A second entry means the pending bit was never cleared. */
    la      t2, timer_seen
    lw      t0, 0(t2)
    bnez    t0, s_stip_storm
    li      t0, 1
    sw      t0, 0(t2)

    la      a0, s_stip_ok
    call    puts

    /*
     * Confirm S-mode cannot acknowledge its own timer interrupt: without
     * Sstc the write to sip.STIP is dropped, so the bit is still set.
     */
    li      t0, 0x20
    csrc    sip, t0
    csrr    t1, sip
    andi    t1, t1, 0x20
    beqz    t1, s_stip_clearable
    la      a0, s_stip_not_clearable
    call    puts
    j       s_stip_arm

s_stip_clearable:
    /* Informative only: Sstc would let S-mode clear it, and the SBI
     * round-trip below would become optional rather than mandatory. */
    la      a0, s_stip_was_clearable
    call    puts

s_stip_arm:
    /*
     * Close the loop the way the kernel will: one SBI set_timer programs
     * the next deadline *and* clears STIP, in M-mode.
     */
    li      a7, 0x54494d45           /* "TIME" */
    li      a0, 0                    /* fid: set_timer */
    li      a1, 0x7fffffffffff0000   /* a deadline far in the future */
    ecall
    bnez    a0, s_fail

    /*
     * Bounded spin: had STIP stayed pending, the interrupt would fire again
     * immediately and land in s_stip_storm.
     */
    li      s1, 1
    slli    s1, s1, 22
1:
    addi    s1, s1, -1
    bnez    s1, 1b

    la      a0, s_stip_closed
    call    puts

    la      t2, timer_done
    li      t0, 1
    sw      t0, 0(t2)

    ld      ra, 0(sp)
    ld      t0, 8(sp)
    ld      t1, 16(sp)
    ld      t2, 24(sp)
    ld      a0, 32(sp)
    ld      a1, 40(sp)
    ld      s0, 48(sp)
    ld      s1, 56(sp)
    addi    sp, sp, 64
    sret

s_stip_storm:
    la      a0, s_stip_storm_msg
    call    puts
    j       exit_fail

s_stip_unexpected:
    la      a0, s_unexpected
    call    puts
    csrr    a0, scause
    call    puthex
    call    putnl
    j       exit_fail

s_timer_timeout:
    la      a0, s_no_timer
    call    puts
    j       exit_fail

/* ------------------------------------------------------------------ */
/* S-mode trap entry for a U-mode trap: the switch window.             */
/* ------------------------------------------------------------------ */
s_trap_u:
    /*
     * The production sequence, verbatim: swap onto the kernel stack, drop
     * translation, and only then touch memory. Nothing between the entry
     * and `sfence.vma` may access memory, because `satp` still names the
     * user table and only the identity-mapped kernel window is keeping the
     * fetch alive.
     */
    csrrw   sp, sscratch, sp
    csrw    satp, zero
    sfence.vma zero, zero
    /* --- translation off: from here on this is ordinary S-mode --- */

    addi    sp, sp, -64
    sd      ra, 0(sp)
    sd      t0, 8(sp)
    sd      t1, 16(sp)
    sd      t2, 24(sp)
    sd      a0, 32(sp)
    sd      a1, 40(sp)
    sd      s0, 48(sp)
    sd      s1, 56(sp)

    csrr    t0, scause
    li      t1, 8                     /* ecall from U-mode */
    bne     t0, t1, s_u_unexpected

    /* SPP must say the trap came from U-mode. */
    csrr    t1, sstatus
    srli    t1, t1, 8
    andi    t1, t1, 1
    bnez    t1, s_u_unexpected

    la      a0, s_u_ok
    call    puts
    /*
     * Reaching the next line is the real proof: the UART is *not* in the
     * user table, so the store inside `puts` can only succeed if `satp`
     * really was cleared above.
     */
    la      a0, s_u_bare
    call    puts

    ld      ra, 0(sp)
    ld      t0, 8(sp)
    ld      t1, 16(sp)
    ld      t2, 24(sp)
    ld      a0, 32(sp)
    ld      a1, 40(sp)
    ld      s0, 48(sp)
    ld      s1, 56(sp)
    addi    sp, sp, 64
    j       s_measure_plic

s_u_unexpected:
    la      a0, s_u_unexpected_msg
    call    puts
    csrr    a0, scause
    call    puthex
    call    putnl
    j       exit_fail

/*
 * The U-mode stub.
 *
 * Only PC-relative control flow and immediates: an absolute `la` here would
 * resolve to a *physical* address, and this code runs at VA 0x0001_0000
 * where only the one 4 KiB user leaf is mapped.
 */
u_stub:
    li      a0, 0x1234
    ecall                            /* cause 8 -> medeleg[8] -> stvec */
1:
    j       1b                       /* not reached */

/* ------------------------------------------------------------------ */
/* Test 7 (informational): can S-mode own the external interrupt?      */
/* ------------------------------------------------------------------ */
s_measure_plic:
    /*
     * MEIP is not delegatable either, so the kernel has two options: drive
     * the PLIC's S-mode context directly (with SEIP delegated), or let
     * M-mode claim the IRQ and inject `mip.SEIP`. Which is available is a
     * property of the machine, not of the source, so it is measured here.
     * A negative answer is reported, not failed: it only selects a
     * different implementation.
     */
    li      t3, 0x0c000028           /* PLIC priority[10] */
    li      t4, 1
    sw      t4, 0(t3)
    li      t3, 0x0c002080           /* PLIC enable[ctx 1] = S-mode hart 0 */
    li      t4, 1 << 10
    sw      t4, 0(t3)
    li      t3, 0x0c201000           /* PLIC threshold[ctx 1] */
    sw      zero, 0(t3)

    /* Ask the UART to raise IRQ 10 on its own: THR-empty interrupt. */
    li      t3, 0x10000001           /* NS16550 IER */
    li      t4, 2
    sb      t4, 0(t3)

    la      t0, s_plic_trap
    csrw    stvec, t0
    li      t0, 0x200                /* sie.SEIE */
    csrs    sie, t0
    li      t0, 0x2                  /* sstatus.SIE */
    csrs    sstatus, t0

    li      s0, 1
    slli    s0, s0, 24
    la      s1, plic_seen
1:
    lw      t0, 0(s1)
    bnez    t0, 2f
    addi    s0, s0, -1
    beqz    s0, s_plic_none
    j       1b
2:
    li      t3, 0x10000001
    sb      zero, 0(t3)              /* quiet the source */
    li      t0, 0x200
    csrc    sie, t0
    j       exit_pass

s_plic_trap:
    addi    sp, sp, -64
    sd      ra, 0(sp)
    sd      t0, 8(sp)
    sd      t1, 16(sp)
    sd      t2, 24(sp)
    sd      t3, 32(sp)
    sd      a0, 40(sp)
    sd      a1, 48(sp)

    csrr    t0, scause
    li      t1, 0x8000000000000009   /* SEIP */
    bne     t0, t1, s_plic_bad

    li      t3, 0x0c201004           /* PLIC claim/complete[ctx 1] */
    lw      t1, 0(t3)
    li      t0, 10
    bne     t1, t0, s_plic_bad
    sw      t1, 0(t3)                /* complete */

    /*
     * Silence the source and stop taking the interrupt, both here rather
     * than after the wait loop: "THR empty" is continuously true, so the
     * IRQ re-asserts the instant it is completed. Left alone this prints
     * one line per interrupt forever and the runner's timeout kills the
     * probe - which is exactly what the first run did.
     */
    li      t3, 0x10000001           /* NS16550 IER */
    sb      zero, 0(t3)
    li      t0, 0x200                /* sie.SEIE */
    csrc    sie, t0

    la      a0, s_plic_ok
    call    puts
    la      t0, plic_seen
    li      t1, 1
    sw      t1, 0(t0)

    ld      ra, 0(sp)
    ld      t0, 8(sp)
    ld      t1, 16(sp)
    ld      t2, 24(sp)
    ld      t3, 32(sp)
    ld      a0, 40(sp)
    ld      a1, 48(sp)
    addi    sp, sp, 64
    sret

s_plic_none:
    la      a0, s_plic_no
    call    puts
    j       exit_pass

s_plic_bad:
    la      a0, s_plic_bad_msg
    call    puts
    j       exit_fail

s_fail:
    la      a0, s_failed
    call    puts
    j       exit_fail

/* ------------------------------------------------------------------ */
/* Exit                                                                */
/* ------------------------------------------------------------------ */
exit_pass:
    la      a0, m_all_ok
    call    puts
    li      t0, 0x5555              /* sifive_test FINISHER_PASS */
    li      t1, 0x100000
    sw      t0, 0(t1)
1:
    j       1b

exit_fail:
    li      t0, 0x3333              /* sifive_test FINISHER_FAIL */
    li      t1, 0x100000
    sw      t0, 0(t1)
1:
    j       1b

    .section .rodata
m_banner:       .asciz "M: boot, misa="
m_got_ecall:    .asciz "M: got ecall, a7="
m_space:        .asciz " a0="
m_delegate:     .asciz "M: delegating exceptions to S-mode\n"
m_satp_effective: .asciz "M: page fault in S-mode - satp is effective\n"
m_instr_fault_msg: .asciz "M: instruction page fault - the fetch was not mapped: FAIL\n"
m_timer_fwd_msg: .asciz "M: forwarding MTIP as mip.STIP\n"
m_soft_fwd_msg:  .asciz "M: forwarding MSIP as mip.SSIP\n"
m_set_timer:     .asciz "M: set_timer wrote mtimecmp and cleared STIP\n"
m_all_ok:       .asciz "PROBE RESULT: PASS (all six S-mode premises hold)\n"
m_unexpected:   .asciz "M: unexpected trap, mcause="
m_root:         .asciz "M: root2/l1_0/leaf0/leaf5/satp = "
s_banner:       .asciz "S: entered, sstatus="
s_ecall_ok:     .asciz "S: ecall round-trip ok\n"
s_delegated:    .asciz "S: delegated trap handled in S-mode\n"
s_deleg_ok:     .asciz "S: stvec/sret delegated path ok\n"
s_about_to_fault: .asciz "S: satp on, UART unmapped, next access must fault\n"
s_unexpected:   .asciz "S: unexpected trap, scause="
s_failed:       .asciz "S: FAILED\n"
s_stip_ok:      .asciz "S: STIP delivered to S-mode (scause=0x8000000000000005)\n"
s_stip_not_clearable: .asciz "S: sip.STIP not clearable in S-mode (expected)\n"
s_stip_was_clearable: .asciz "S: sip.STIP was clearable in S-mode (Sstc present)\n"
s_stip_closed:  .asciz "S: SBI set_timer closed the loop - no STIP storm\n"
s_stip_storm_msg: .asciz "S: STIP storm - the pending bit was never cleared: FAIL\n"
s_no_timer:     .asciz "S: no STIP arrived - the timer forward is broken: FAIL\n"
s_u_ok:         .asciz "S: U-mode trap taken in S-mode (scause=8, SPP=0)\n"
s_u_bare:       .asciz "S: satp switch window ok - UART reachable after csrw satp,zero\n"
s_u_unexpected_msg: .asciz "S: unexpected U-mode trap, scause="
s_plic_ok:      .asciz "S: PLIC S-context works - SEIP claimed irq 10\n"
s_plic_no:      .asciz "S: SEIP not delivered (PLIC S-context unavailable)\n"
s_plic_bad_msg: .asciz "S: unexpected external interrupt: FAIL\n"

    .section .bss
    .balign 4096
m_stack:
    .space 4096
m_stack_top:

    .balign 4096
s_stack:
    .space 4096
s_stack_top:

    .balign 4096
root_pte:
    .space 4096
l1_pte:
    .space 4096
leaf_pte:
    .space 4096

/* The U-mode table for the switch-window test: one 4 KiB user leaf plus
 * the 2 MiB kernel window, both rooted in `u_root`. */
    .balign 4096
u_root:
    .space 4096
u_l1u:
    .space 4096
u_leafu:
    .space 4096
u_l1k:
    .space 4096

    .balign 8
m_saved:
    .space 232
timer_seen:
    .space 4
timer_done:
    .space 4
plic_seen:
    .space 4
