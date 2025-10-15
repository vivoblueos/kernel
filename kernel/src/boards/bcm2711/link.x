OUTPUT_FORMAT("elf64-littleaarch64", "elf64-littleaarch64", "elf64-littleaarch64")
OUTPUT_ARCH(aarch64)

STACK_SIZE = 128 * 1024;

MEMORY
{
	DRAM : ORIGIN = 0x80000, LENGTH = 32M
}

PHDRS
{
  /* R = 100, W = 010, X = 001 */

  text   PT_LOAD FLAGS(5); /* RX */
  rodata PT_LOAD FLAGS(4); /* R  */
  data   PT_LOAD FLAGS(6); /* RW */
}

ENTRY(_start)
SECTIONS
{
    __binary_address_start = 0x80000 ;
    .text :
    {
        __text_start = .;
        _start = .;
        KEEP(*(.text._start))
        KEEP(*(.text._startup_el1))
        KEEP(*(.text.vector_table))
        KEEP(*(.text._exception))
        *(.text*)
        __text_end = .;
    } > DRAM :text

    .rodata : ALIGN(4096)
    {
        __rodata_start = .;
        *(.rodata*)
        __rodata_end = .;
    } > DRAM :rodata

    .data : ALIGN(4096)
    {
        __data_start = .;
        *(.data*)
        __data_end = .;
    } > DRAM :data

    .bss : ALIGN(4096)
    {
        __bss_start = .;
        *(.bss*)
        __bss_end = .;
    } > DRAM :data

    .init_array : {
      . = ALIGN(16);
      PROVIDE_HIDDEN (__init_array_start = .);
      KEEP (*(SORT_BY_INIT_PRIORITY(.init_array.*)))
      KEEP (*(.init_array))
      PROVIDE_HIDDEN (__init_array_end = .);
    } > DRAM :data

    .bk_app_array : {
      . = ALIGN(16);
      PROVIDE_HIDDEN (__bk_app_array_start = .);
      KEEP (*(SORT_BY_INIT_PRIORITY(.bk_app_array.*)))
      KEEP (*(.bk_app_array))
      PROVIDE_HIDDEN (__bk_app_array_end = .);
    } > DRAM :data

    __binary_address_end = . ;

    .stack : ALIGN(4096)
    {
        __sys_stack_start = .;
        . += STACK_SIZE;
        __sys_stack_end = .;
    } > DRAM :data


    . = ALIGN(4096);
    __heap_start = .;
    . += 0x800000;
    __heap_end = .;
    _end = .;
}
