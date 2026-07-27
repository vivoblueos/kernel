OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
  RTC_FAST (rwx) : ORIGIN = 0x50000000, LENGTH = 0x2000
}

PHDRS
{
  text PT_LOAD FLAGS(5);
  data PT_LOAD FLAGS(6);
}

SECTIONS
{
  .text : ALIGN(4)
  {
    KEEP(*(.text._start))
    *(.text .text.*)
    *(.rodata .rodata.*)
  } > RTC_FAST :text

  .data : ALIGN(4)
  {
    *(.sdata .sdata.*)
    *(.data .data.*)
  } > RTC_FAST :data

  .bss (NOLOAD) : ALIGN(4)
  {
    *(.sbss .sbss.*)
    *(.bss .bss.*)
    *(COMMON)
  } > RTC_FAST :data

  /DISCARD/ :
  {
    *(.eh_frame*)
    *(.comment*)
  }

  ASSERT(SIZEOF(.text) > 0, "EXEC payload has no text")
  ASSERT(. <= ORIGIN(RTC_FAST) + LENGTH(RTC_FAST), "EXEC payload exceeds RTC_FAST")
}
