OUTPUT_FORMAT("elf64-littleaarch64", "elf64-littleaarch64", "elf64-littleaarch64")
OUTPUT_ARCH(aarch64)

#include <autoconf.h>

#define STACK_SIZE (CONFIG_STACK_SIZE * 1K)
#define KERNEL_BASE (CONFIG_KERNEL_VIRT_OFFSET + CONFIG_KERNEL_PHYS_BASE)

ENTRY(_start_load)

SECTIONS
{
    . = KERNEL_BASE;

    .text : AT(CONFIG_KERNEL_PHYS_BASE) ALIGN(4096) {
        __text_start = .;
        _start = .;
        KEEP(*(.text._start))
        KEEP(*(.text._startup_el1))
        KEEP(*(.text.vector_table))
        KEEP(*(.text._exception))
        KEEP(*(.text.hyper_vector_table))
        *(.text*)
        __text_end = .;
    }
    _start_load = LOADADDR(.text);

    .rodata : ALIGN(4096) {
        __rodata_start = .;
        *(.rodata*)
        __rodata_end = .;
    }

    .data : ALIGN(4096) {
        __data_start = .;
        *(.data*)
        __data_end = .;
    }

    .bss : ALIGN(4096)
    {
        __bss_start = .;
        *(.bss*)
        __bss_end = .;
    }

    .init_array : {
      . = ALIGN(16);
      PROVIDE_HIDDEN (__init_array_start = .);
      KEEP (*(SORT_BY_INIT_PRIORITY(.init_array.*)))
      KEEP (*(.init_array))
      PROVIDE_HIDDEN (__init_array_end = .);
    }

    .bk_app_array : {
      . = ALIGN(16);
      PROVIDE_HIDDEN (__bk_app_array_start = .);
      KEEP (*(SORT_BY_INIT_PRIORITY(.bk_app_array.*)))
      KEEP (*(.bk_app_array))
      PROVIDE_HIDDEN (__bk_app_array_end = .);
    }

    .stack : ALIGN(4096)
    {
        __sys_stack_start = .;
        . += STACK_SIZE;
        __sys_stack_end = .;
    }


    . = ALIGN(4096);
    __heap_start = .;
    . += 0x2000000;
    __heap_end = .;
    _end = .;
}