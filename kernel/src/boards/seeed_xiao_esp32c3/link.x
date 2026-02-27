/* This code is derived from
 * https://github.com/esp-rs/esp-hal/tree/main/esp-hal/ld/esp32c3
 * Copyright 2021 esp-rs
 * License: Apache-2.0 OR MIT
 */

OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
    /*
        https://github.com/espressif/esptool/blob/ed64d20b051d05f3f522bacc6a786098b562d4b8/esptool/targets/esp32c3.py#L78-L90
        MEMORY_MAP = [[0x00000000, 0x00010000, "PADDING"],
                  [0x3C000000, 0x3C800000, "DROM"],
                  [0x3FC80000, 0x3FCE0000, "DRAM"],
                  [0x3FC88000, 0x3FD00000, "BYTE_ACCESSIBLE"],
                  [0x3FF00000, 0x3FF20000, "DROM_MASK"],
                  [0x40000000, 0x40060000, "IROM_MASK"],
                  [0x42000000, 0x42800000, "IROM"],
                  [0x4037C000, 0x403E0000, "IRAM"],
                  [0x50000000, 0x50002000, "RTC_IRAM"],
                  [0x50000000, 0x50002000, "RTC_DRAM"],
                  [0x600FE000, 0x60100000, "MEM_INTERNAL2"]]
    */

    ICACHE : ORIGIN = 0x4037C000,  LENGTH = 0x4000
    /* Instruction RAM */
    IRAM : ORIGIN = 0x4037C000 + 0x4000, LENGTH = 313K - 0x4000
    /* Data RAM */
    DRAM : ORIGIN = 0x3FC80000, LENGTH = 313K
    
    /* memory available after the 2nd stage bootloader is finished */
    dram2_seg ( RW )       : ORIGIN = ORIGIN(DRAM) + LENGTH(DRAM), len = 0x3fcde710 - (ORIGIN(DRAM) + LENGTH(DRAM))

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
    DROM (rxai!w) : ORIGIN = 0x3C000000 + 0x20, LENGTH = 0x400000 - 0x20

    /* RTC fast memory (executable). Persists over deep sleep. */
    RTC_FAST : ORIGIN = 0x50000000, LENGTH = 0x2000 /*- ESP_BOOTLOADER_RESERVE_RTC*/    
}

REGION_ALIAS("ROTEXT", IROM);
REGION_ALIAS("RODATA", DROM);

REGION_ALIAS("RWDATA", DRAM);
REGION_ALIAS("RWTEXT", IRAM);

REGION_ALIAS("RTC_FAST_RWTEXT", RTC_FAST);
REGION_ALIAS("RTC_FAST_RWDATA", RTC_FAST);

SECTIONS {
  .trap : ALIGN(4)
  {
    _trap_section_origin = .;
    KEEP(*(.trap));
    *(.trap.*);
  } > RWTEXT

  .rwtext : ALIGN(4)
  {
    . = ALIGN (4);
    *(.rwtext.literal .rwtext .rwtext.literal.* .rwtext.*)
    /* unconditionally add patched SPI-flash ROM functions (from esp-rom-sys) - the linker is still happy if there are none */
    *:esp_rom_spiflash.*(.literal .literal.* .text .text.*)
    . = ALIGN(4);
  } > RWTEXT

  .rwtext.wifi :
  {
    . = ALIGN(4);
    *( .wifi0iram  .wifi0iram.*)
    *( .wifirxiram  .wifirxiram.*)
    *( .wifislprxiram  .wifislprxiram.*)
    *( .wifislpiram  .wifislpiram.*)
    *( .phyiram  .phyiram.*)
    *( .iram1  .iram1.*)
    *( .wifiextrairam.* )
    *( .coexiram.* )
    . = ALIGN(4);

    _rwtext_len = . - ORIGIN(RWTEXT);
  } > RWTEXT

  .rwdata_dummy (NOLOAD) : ALIGN(4)
  {
    . = . + SIZEOF(.rwtext) + SIZEOF(.rwtext.wifi) + SIZEOF(.trap);
  } > RWDATA

  .data : ALIGN(4)
  {
    _data_start = ABSOLUTE(.);
    . = ALIGN (4);

    *(.rodata.*_esp_hal_internal_handler*)
    *(.rodata..Lswitch.table.*)
    *(.rodata.cst*)


    *(.sdata .sdata.* .sdata2 .sdata2.*);
    *(.data .data.*);
    *(.data1)
    _data_end = ABSOLUTE(.);
    . = ALIGN(4);
  } > RWDATA

  .data.wifi :
  {
    . = ALIGN(4);
    *( .dram1 .dram1.*)
    . = ALIGN(4);
  } > RWDATA

  .bss (NOLOAD) : ALIGN(4)
  {
    __bss_start = ABSOLUTE(.);
    . = ALIGN (4);
    *(.dynsbss)
    *(.sbss)
    *(.sbss.*)
    *(.gnu.linkonce.sb.*)
    *(.scommon)
    *(.sbss2)
    *(.sbss2.*)
    *(.gnu.linkonce.sb2.*)
    *(.dynbss)
    *(.sbss .sbss.* .bss .bss.*);
    *(.share.mem)
    *(.gnu.linkonce.b.*)
    *(COMMON)
    __bss_end = ABSOLUTE(.);
    . = ALIGN(4);
  } > RWDATA

  .noinit (NOLOAD) : ALIGN(4)
  {
    . = ALIGN(4);
    *(.noinit .noinit.*)
    *(.uninit .uninit.*)
    . = ALIGN(4);
  } > RWDATA
}

SECTIONS {
  /* For ESP App Description, must be placed first in image */
  .rodata_desc : ALIGN(0x10)
  {
      KEEP(*(.rodata_desc));
      KEEP(*(.rodata_desc.*));
  } > RODATA

  .rodata : ALIGN(0x10)
  {
    . = ALIGN (4);
    _rodata_start = ABSOLUTE(.);
    *(.rodata .rodata.*)
    *(.srodata .srodata.*)
    . = ALIGN(4);

    PROVIDE_HIDDEN(__bk_app_array_start = .);
    KEEP (*(SORT_BY_INIT_PRIORITY(.bk_app_array.*)))
    KEEP (*(.bk_app_array))
    PROVIDE_HIDDEN(__bk_app_array_end = .);

    . = ALIGN(4);
    PROVIDE(__init_array_start = .);
    KEEP (*(SORT_BY_INIT_PRIORITY(.init_array.*)))
    KEEP (*(EXCLUDE_FILE (*crtend.* *crtbegin.*) .init_array))
    PROVIDE(__init_array_end = .);
    . = ALIGN(4);
    _rodata_end = ABSOLUTE(.);
  } > RODATA  
}

SECTIONS {
  .rotext_dummy (NOLOAD) :
  {
    /* This dummy section represents the .rodata section within ROTEXT.
    * Since the same physical memory is mapped to both DROM and IROM,
    * we need to make sure the .rodata and .text sections don't overlap.
    * We skip the amount of memory taken by .rodata* in .text
    */

    /* Start at the same alignment constraint than .flash.text */

    . = ALIGN(ALIGNOF(.rodata));

    /* Create an empty gap as big as .text section */

    . = . + SIZEOF(.rodata_desc);
    . = . + SIZEOF(.rodata);

    /* Prepare the alignment of the section above. Few bytes (0x20) must be
     * added for the mapping header.
     */

    . = ALIGN(0x10000) + 0x20;
    _rotext_reserved_start = .;
  } > ROTEXT

  .text : ALIGN(4)
  {
    KEEP(*(.init));
    KEEP(*(.init.rust));
    KEEP(*(.text.abort));
    *(.literal .text .literal.* .text.*)
  } > ROTEXT
}

SECTIONS {
  .rtc_fast.text : {
   . = ALIGN(4);
   *(.rtc_fast.literal .rtc_fast.text .rtc_fast.literal.* .rtc_fast.text.*)
   . = ALIGN(4);
  } > RTC_FAST_RWTEXT AT > RODATA

  .rtc_fast.data :
  {
    . = ALIGN(4);
    _rtc_fast_data_start = ABSOLUTE(.);
    *(.rtc_fast.data .rtc_fast.data.*)
    _rtc_fast_data_end = ABSOLUTE(.);
    . = ALIGN(4);
  } > RTC_FAST_RWDATA AT > RODATA

  /* LMA of .data */
  _rtc_fast_sidata = LOADADDR(.rtc_fast.data);

 .rtc_fast.bss (NOLOAD) :
  {
    . = ALIGN(4);
    _rtc_fast_bss_start = ABSOLUTE(.);
    *(.rtc_fast.bss .rtc_fast.bss.*)
    _rtc_fast_bss_end = ABSOLUTE(.);
    . = ALIGN(4);
  } > RTC_FAST_RWDATA

 .rtc_fast.persistent (NOLOAD) :
  {
    . = ALIGN(4);
    _rtc_fast_persistent_start = ABSOLUTE(.);
    *(.rtc_fast.persistent .rtc_fast.persistent.*)
    _rtc_fast_persistent_end = ABSOLUTE(.);
    . = ALIGN(4);
  } > RTC_FAST_RWDATA
}

SECTIONS
{
  .heap (NOLOAD) : {
    . = ALIGN(8);
    __heap_start = .;
    . = ORIGIN(DRAM) + LENGTH(DRAM) - 0x1000;
    __heap_end = .;
  } > RWDATA

  .stack (NOLOAD) : {
    . = ALIGN(16);
    __sys_stack_start = .;
    . += 0x1000;
    __sys_stack_end = .;
  } > RWDATA
}

SECTIONS {
  .espressif.metadata 0 (INFO) :
  {
    KEEP(*(.espressif.metadata));
  }
}

SECTIONS {
  .eh_frame 0 (INFO) :
  {
    KEEP(*(.eh_frame));
  }
}

PROVIDE(__global_pointer$ = ALIGN(_data_start, 4) + 0x800);
