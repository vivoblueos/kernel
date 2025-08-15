/*
 * Copyright (c) 2009-2019 Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the License); you may
 * not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an AS IS BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

MEMORY {
    /*
     * The RP2350 has either external or internal flash.
     *
     * 2 MiB is a safe default here, although a Pico 2 has 4 MiB.
     */
    FLASH : ORIGIN = 0x10000000, LENGTH = 4096K
    /*
     * RAM consists of 8 banks, SRAM0-SRAM7, with a striped mapping.
     * This is usually good for performance, as it distributes load on
     * those banks evenly.
     */
    RAM : ORIGIN = 0x20000000, LENGTH = 512K
    /*
     * RAM banks 8 and 9 use a direct mapping. They can be used to have
     * memory areas dedicated for some specific job, improving predictability
     * of access times.
     * Example: Separate stacks for core0 and core1.
     */
    SRAM4 : ORIGIN = 0x20080000, LENGTH = 4K
    SRAM5 : ORIGIN = 0x20081000, LENGTH = 4K
}

STACK_SIZE = 0x00004000;

ENTRY(_start)
EXTERN(__EXCEPTION_HANDLERS__)
EXTERN(__INTERRUPT_HANDLERS__)

SECTIONS
{
  .vector_table ORIGIN(FLASH) :
  {
    __vector_table_start = .;
    LONG(__init_msp);
    /* We have to put reference of _start in vector.exceptions. */
    KEEP(*(.exception.handlers));
    KEEP(*(.interrupt.handlers));
    __vector_table_end = .;
  } > FLASH

  .start_block : ALIGN(4)
  {
    __start_block_addr = .;
    KEEP(*(.start_block));
    KEEP(*(.boot_info));
  } > FLASH

  PROVIDE(_stext = ADDR(.start_block) + SIZEOF(.start_block));

  /* ### .text */
  .text _stext :
  {
    . = ALIGN(4);
    __stext = .;
    *(.text .text.*);
  } > FLASH

  .bi_entries : ALIGN(4)
  {
    /* We put this in the header */
    __bi_entries_start = .;
    /* Here are the entries */
    KEEP(*(.bi_entries));
    /* Keep this block a nice round size */
    . = ALIGN(4);
    /* We put this in the header */
    __bi_entries_end = .;
  } > FLASH

  /* ### .rodata */
  .rodata : ALIGN(4)
  {
    . = ALIGN(4);
    __srodata = .;
    __rodata_start = .;
    *(.rodata .rodata.*);
    . = ALIGN(4);
    __rodata_end = .;
    __erodata = .;
  } > FLASH

  .ARM.extab :
  {
    *(.ARM.extab* .gnu.linkonce.armextab.*)
  } > FLASH

  __exidx_start = .;
  .ARM.exidx :
  {
    *(.ARM.exidx* .gnu.linkonce.armexidx.*)
  } > FLASH
  __exidx_end = .;

  /* Put .bss to RAM */
  .zero.table :
  {
    . = ALIGN(4);
    __zero_table_start = .;
    LONG (__bss_start)
    LONG ((__bss_end - __bss_start) / 4)
    __zero_table_end = .;
  } > FLASH

  /* Put .data to RAM */
  .copy.table :
  {
    . = ALIGN(4);
    __copy_table_start = .;
    LONG (__etext)
    LONG (__data_start)
    LONG ((__data_end - __data_start) / 4)
    __copy_table_end = .;
  } > FLASH
  
  __etext = ALIGN(4);

  .data : AT (__etext)
  {
    . = ALIGN(4);
    __data_start = .;
    __sdata = .;
    *(vtable)
    *(.data)
    *(.data.*)

    . = ALIGN(4);
    PROVIDE_HIDDEN (__preinit_array_start = .);
    KEEP(*(.preinit_array))
    PROVIDE_HIDDEN (__preinit_array_end = .);

    . = ALIGN(4);
    PROVIDE_HIDDEN (__init_array_start = .);
    KEEP(*(SORT(.init_array.*)))
    KEEP(*(.init_array))
    PROVIDE_HIDDEN (__init_array_end = .);

    . = ALIGN(4);
    PROVIDE_HIDDEN (__fini_array_start = .);
    KEEP(*(SORT(.fini_array.*)))
    KEEP(*(.fini_array))
    PROVIDE_HIDDEN (__fini_array_end = .);

    . = ALIGN(4);
    PROVIDE_HIDDEN (__bk_app_array_start = .);
    KEEP(*(SORT(.bk_app_array.*)))
    KEEP(*(.bk_app_array))
    PROVIDE_HIDDEN (__bk_app_array_end = .);

    KEEP(*(.jcr*))
    . = ALIGN(4);
    __data_end = .;
    __edata = .;
  } > RAM

  /* LMA of .data */
  __sidata = LOADADDR(.data);

  .bss :
  {
    . = ALIGN(4);
    __bss_start = .;
    __sbss = .;
    *(.bss)
    *(.bss.*)
    *(COMMON)
    . = ALIGN(4);
    __bss_end = .;
    __ebss = .;
  } > RAM

  .heap (COPY) :
  {
    . = ALIGN(8);
    PROVIDE(_end = .);
    __heap_start = .;
    . = ORIGIN(RAM) + LENGTH(RAM) - STACK_SIZE;
    . = ALIGN(8);
    __heap_end = .;
  } > RAM

  .stack (ORIGIN(RAM) + LENGTH(RAM) - STACK_SIZE) (COPY) :
  {
    . = ALIGN(8);
    __sys_stack_start = .;
    . = . + STACK_SIZE;
    . = ALIGN(8);
    __sys_stack_end = .;
  } > RAM
  PROVIDE(__init_msp = __sys_stack_end);

  /DISCARD/ :
  {
    *(.ARM.exidx);
    *(.ARM.exidx.*);
    *(.ARM.extab.*);
    *(.ARM.extab);
    *(.noinit);
  }

  ASSERT(__sys_stack_start >= __heap_end, "Stack and heap overlap each other!")
}
