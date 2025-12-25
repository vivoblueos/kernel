/**
 * Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

#include <autoconf.h>

#define RAM_SIZE (CONFIG_SRAM_SIZE * 1K)
#define RAM_BASE CONFIG_SRAM_BASE_ADDRESS
#define STACK_SIZE (CONFIG_STACK_SIZE * 1K)
#define ROM_BASE CONFIG_FLASH_BASE_ADDRESS
#define ROM_SIZE (CONFIG_FLASH_SIZE * 1K)

MEMORY
{
  FLASH (rx) : ORIGIN = ROM_BASE, LENGTH = ROM_SIZE
  RAM (rwx) : ORIGIN = RAM_BASE, LENGTH = RAM_SIZE
}

#ifdef CONFIG_KERNEL_ENTRY
ENTRY(CONFIG_KERNEL_ENTRY)
#else
ENTRY(_start)
#endif

EXTERN(__EXCEPTION_HANDLERS__)
EXTERN(__INTERRUPT_HANDLERS__)

SECTIONS
{
  .vector_table ORIGIN(FLASH) :
  {
    __vector_table_start = .;
    LONG(__init_msp);
    /* We have to put reference of _start in vector.exceptions. */
    KEEP(*(.exception.vectors));
    KEEP(*(.interrupt.vectors));
    __vector_table_end = .;
  } > FLASH

  .text :
  {
    . = ALIGN(4);
    *(.text*)
  } > FLASH

  . = ALIGN(4);
  __rodata_start = .;
  .rodata : { *(.rodata*) } > FLASH
  __rodata_end = .;

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

  __etext = ALIGN (4);

  .data : AT (__etext)
  {
    __data_start = .;
    . = ALIGN(4);
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

    . = ALIGN(4);
    __start___llvm_prf_cnts = .;
    KEEP(*(__llvm_prf_cnts))
    __stop___llvm_prf_cnts = .;

    . = ALIGN(4);
    __start___llvm_prf_data = .;
    KEEP(*(__llvm_prf_data))
    __stop___llvm_prf_data = .;

    KEEP(*(.jcr*))
    . = ALIGN(4);
    __data_end = .;

  } > RAM

  .bss :
  {
    . = ALIGN(4);
    __bss_start = .;
    *(.bss)
    *(.bss.*)
    *(COMMON)
    . = ALIGN(4);
    __bss_end = .;
  } > RAM AT > RAM

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
