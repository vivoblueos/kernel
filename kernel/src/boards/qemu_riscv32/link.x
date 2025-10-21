/* This code is derived from
 * https://github.com/eclipse-threadx/threadx/blob/master/ports/risc-v64/gnu/example_build/qemu_virt/link.lds
 * Copyright (c) 2024 - present Microsoft Corporation
 * SPDX-License-Identifier: MIT
 */

OUTPUT_ARCH("riscv")
ENTRY(_start)

SECTIONS
{
  /*
   * ensure that entry.S / _entry is at 0x80000000,
   * where qemu's -kernel jumps.
   */
  . = 0x80000000;

  /* Ignore build information, like .hash, .gnu.hash and etc. */

  .text : {
    . = ALIGN(16);
    *(.text._start)
    *(.text .text.*)
    . = ALIGN(0x1000);
    PROVIDE(etext = .); 
  }

  .rodata : {
    . = ALIGN(16);
    *(.srodata .srodata.*) /* do not need to distinguish this from .rodata */
    . = ALIGN(16);
    *(.rodata .rodata.*)
  }

  .data : {
    . = ALIGN(16);
    *(.sdata .sdata.*) /* do not need to distinguish this from .data */
    . = ALIGN(16);
    *(.data .data.*)
  }

  .bss : {
    . = ALIGN(16);
    __bss_start = .;
    *(.sbss .sbss.*) /* do not need to distinguish this from .bss */
    . = ALIGN(16);
    *(.bss .bss.*)
    __bss_end = .;
  }

  /* Initialize C runtime. */
  /* .ctors and .dtors should not appear since we don't have C++ code at present. */
  .init_array : {
    . = ALIGN(16);
    PROVIDE_HIDDEN(__init_array_start = .);
    KEEP (*(SORT_BY_INIT_PRIORITY(.init_array.*)))
    KEEP (*(.init_array))
    PROVIDE_HIDDEN(__init_array_end = .);
  }

  .bk_app_array : {
    . = ALIGN(16);
    PROVIDE_HIDDEN(__bk_app_array_start = .);
    KEEP (*(SORT_BY_INIT_PRIORITY(.bk_app_array.*)))
    KEEP (*(.bk_app_array))
    PROVIDE_HIDDEN(__bk_app_array_end = .);
  }

  .heap : {
    . = ALIGN(4096);
    __heap_start = .;
    . += 0x800000;
    __heap_end = .;
  }

  /* Ignore .fini_array since we are building a kernel which has no chance to
   * execute code in .fini_array. */

  .stack : {
    . = ALIGN(16);
    __sys_stack_start = .;
    . += 0x80000;
    __sys_stack_end = .;
  }

  PROVIDE(_end = .);
}
