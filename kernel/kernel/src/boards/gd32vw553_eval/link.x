/*
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

OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY {
  FLASH (rxai!w) : ORIGIN = 0x08000000, LENGTH = 4096K
  RAM (wxa!ri) : ORIGIN = 0x20000000, LENGTH = 320K
}

SYSTEM_STACK_SIZE = 0x1000;

SECTIONS
{
  .text : {
    . = ALIGN(4);
    *(.text._start)
    *(.text .text.*)
  } >FLASH AT>FLASH

  .rodata : {
    . = ALIGN(4);
    *(.srodata .srodata.*)
    *(.rodata .rodata.*)
  } >FLASH AT>FLASH

  .init_array : {
    . = ALIGN(4);
    PROVIDE_HIDDEN(__init_array_start = .);
    KEEP (*(SORT_BY_INIT_PRIORITY(.init_array.*)))
    KEEP (*(.init_array))
    PROVIDE_HIDDEN(__init_array_end = .);
  } >FLASH AT>FLASH

  .bk_app_array : {
    . = ALIGN(4);
    PROVIDE_HIDDEN(__bk_app_array_start = .);
    KEEP (*(SORT_BY_INIT_PRIORITY(.bk_app_array.*)))
    KEEP (*(.bk_app_array))
    PROVIDE_HIDDEN(__bk_app_array_end = .);
  } >FLASH AT>FLASH

  .data_on_flash : {
    . = ALIGN(4);
    PROVIDE(__data_lma = .);
  } >FLASH AT>FLASH

  .data_on_ram : {
    . = ALIGN(4);
    PROVIDE(__data_start = .);
  } >RAM AT>FLASH

  .data : {
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
  } >RAM AT>FLASH
  . = ALIGN(4);
  PROVIDE(__data_end = .);

  .bss : {
    . = ALIGN(4);
    __bss_start = .;
    *(.sbss .sbss.*)
    *(.bss .bss.*)
    . = ALIGN(4);
    __bss_end = .;
  } >RAM

  .heap : {
    . = ALIGN(16);
    __heap_start = .;
    . = ORIGIN(RAM) + LENGTH(RAM) - SYSTEM_STACK_SIZE;
    __heap_end = .;
  } >RAM

  .stack : {
    . = ALIGN(8);
    __sys_stack_start = .;
    . = ORIGIN(RAM) + LENGTH(RAM);
    __sys_stack_end = .;
  } >RAM

  PROVIDE(_end = .);
}
