/* This code is derived from
 * https://github.com/eclipse-threadx/threadx/blob/master/ports/risc-v64/gnu/example_build/qemu_virt/link.lds
 * Copyright (c) 2024 - present Microsoft Corporation
 * SPDX-License-Identifier: MIT
 */

OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY {
    /* External flash

     The 0x20 offset is a convenience for the app binary image generation.
     Flash cache has 64KB pages. The .bin file which is flashed to the chip
     has a 0x18 byte file header, and each segment has a 0x08 byte segment
     header. Setting this offset makes it simple to meet the flash cache MMU's
     constraint that (paddr % 64KB == vaddr % 64KB).)
    */    

    /* Instruction ROM */
    IROM : ORIGIN =   0x42000000 + 0x20, LENGTH = 0x400000 - 0x20
    /* Data ROM */
    DROM : ORIGIN = 0x3C000000 + 0x20, LENGTH = 0x400000 - 0x20

    DRAM : ORIGIN = 0x3FC80000, LENGTH = 384K
}

SECTIONS
{
  .rodata_desc : ALIGN(4)
  {
      KEEP(*(.rodata_desc));
      KEEP(*(.rodata_desc.*));
  } > DROM

  .rodata : ALIGN(4)
  {
    . = ALIGN(16);
    *(.srodata .srodata.*) /* do not need to distinguish this from .rodata */
    . = ALIGN(16);
    *(.rodata .rodata.*)
  } > DROM

  .rodata.wifi : ALIGN(4)
  {
    . = ALIGN(4);
    *( .rodata_wlog_*.* )
    . = ALIGN(4);
  } > DROM

  .init_array : {
    . = ALIGN(4);
    PROVIDE_HIDDEN(__init_array_start = .);
    KEEP (*(SORT_BY_INIT_PRIORITY(.init_array.*)))
    KEEP (*(.init_array))
    PROVIDE_HIDDEN(__init_array_end = .);
  } > DROM

  .bk_app_array : {
    . = ALIGN(4);
    PROVIDE_HIDDEN(__bk_app_array_start = .);
    KEEP (*(SORT_BY_INIT_PRIORITY(.bk_app_array.*)))
    KEEP (*(.bk_app_array))
    PROVIDE_HIDDEN(__bk_app_array_end = .);
  } > DROM

  /* Put .bss to RAM */
  .zero.table :
  {
    . = ALIGN(4);
    __zero_table_start = .;
    LONG (__bss_start)
    LONG ((__bss_end - __bss_start) / 4)
    __zero_table_end = .;
  } > DROM

  . = ALIGN(0x10000) + 0x20;
  .text : ALIGN(4)
  {
    *(.literal .text .literal.* .text.*)
  } > IROM

  .data (COPY) : {
    *(.rdata)
    *(.gnu.linkonce.r.*)
    *(.data .data.*)
    *(.gnu.linkonce.d.*)
    . = ALIGN(8);
    PROVIDE(__global_pointer$ = . + 0x800);
    *(.sdata .sdata.*)
    *(.gnu.linkonce.s.*)
    . = ALIGN(8);
    *(.srodata.cst16)
    *(.srodata.cst8)
    *(.srodata.cst4)
    *(.srodata.cst2)
    *(.srodata .srodata.*)
    KEEP(*(.test_data.*));
  } > DRAM
  . = ALIGN(4);
  PROVIDE(__data_end = .);

  .bss : {
    . = ALIGN(4);
    __bss_start = .;
    *(.sbss .sbss.*)
    *(.bss .bss.*)
    . = ALIGN(4);
    __bss_end = .;
  } > DRAM

  .heap : {
    . = ALIGN(8);
    __heap_start = .;
    . = ORIGIN(DRAM) + LENGTH(DRAM) - 0x1000;
    __heap_end = .;
  } > DRAM

  .stack : {
    . = ALIGN(16);
    __sys_stack_start = .;
    . += 0x1000;
    __sys_stack_end = .;
  } > DRAM
}