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

.syntax unified
.thumb

.section .text.boot, "ax"
.align 2
.global cortex_m_boot_entry
.type cortex_m_boot_entry, %function
.thumb_func
cortex_m_boot_entry:
    /* Keep interrupts disabled until the runtime state is initialized. */
    cpsid i

    /* Copy initialized data from its load address in flash to RAM. */
    ldr r0, =__copy_table_start
    ldr r1, =__copy_table_end

.Lcopy_table_loop:
    cmp r0, r1
    bhs .Lcopy_table_done

    ldr r2, [r0], #4
    ldr r3, [r0], #4
    ldr r4, [r0], #4

    /* Each copy table entry contains source, destination, and word count. */
.Lcopy_words_loop:
    cmp r4, #0
    beq .Lcopy_table_loop
    ldr r5, [r2], #4
    str r5, [r3], #4
    subs r4, r4, #1
    b .Lcopy_words_loop

.Lcopy_table_done:
    /* Clear zero-initialized data in RAM. */
    ldr r0, =__zero_table_start
    ldr r1, =__zero_table_end

.Lzero_table_loop:
    cmp r0, r1
    bhs .Lzero_table_done

    ldr r2, [r0], #4
    ldr r3, [r0], #4
    movs r4, #0

    /* Each zero table entry contains destination and word count. */
.Lzero_words_loop:
    cmp r3, #0
    beq .Lzero_table_loop
    str r4, [r2], #4
    subs r3, r3, #1
    b .Lzero_words_loop

.Lzero_table_done:
    /* Switch MSP to the top of the kernel system stack. */
    ldr r0, =__sys_stack_end
    msr msp, r0
    dsb
    isb

    /* Continue in Rust after the basic runtime state is ready. */
    b pre_init

.size cortex_m_boot_entry, . - cortex_m_boot_entry
