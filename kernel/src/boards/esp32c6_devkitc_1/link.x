/* This code is derived from esp-hal's esp32c6 link script
 * (https://github.com/esp-rs/esp-hal/tree/main/esp-hal/ld/esp32c6) and the
 * seeed_xiao_esp32c3 link.x in this repo.
 * Copyright 2021 esp-rs
 * License: Apache-2.0 OR MIT
 */

OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
    /*
        C6 memory map (from external/vendor/esp-hal-1.1.1/ld/esp32c6/memory.x):
        - A single HP RAM segment (no C3-style IRAM/DRAM split): both code and
          data live in RAM, so RWTEXT and RWDATA alias the same region.
        - RTC_FAST is 16K on C6 (C3 had 8K).

        esptool C6 MEMORY_MAP (for reference):
          DROM  0x42800000
          DRAM  0x40800000
          IROM  0x42000000
          RTC_IRAM/RTC_DRAM 0x50000000
    */

    /* Unified HP RAM: executable + readable + writable */
    RAM : ORIGIN = 0x40800000, LENGTH = 0x6E610

    /* External flash.

     The 0x20 offset is a convenience for the app binary image generation.
     Flash cache has 64KB pages. The .bin file which is flashed to the chip
     has a 0x18 byte file header, and each segment has a 0x08 byte segment
     header. Setting this offset makes it simple to meet the flash cache MMU's
     constraint that (paddr % 64KB == vaddr % 64KB).)
    */

    /* On C6 the bootloader maps a single flash window at 0x42000000 for both
       code and rodata (unlike C3, where DROM 0x3C000000 < IROM 0x42000000 are
       separate windows). esptool writes image segments in ascending vaddr
       order, and the bootloader requires the app description to be the first
       segment after the image header. With two regions (IROM 0x42000000,
       DROM 0x42800000) the .text segment ends up before .rodata_desc and the
       app_desc magic is no longer at the start of the partition, producing
       "Failed to fetch app description header" / "not bootable".

       The fix mirrors upstream esp-hal (esp32c6/memory.x): a single ROM region
       aliased to both ROTEXT and RODATA, with .rotext_dummy reserving the
       rodata footprint inside it so the two do not overlap. */
    ROM : ORIGIN = 0x42000000 + 0x20, LENGTH = 0x400000 - 0x20

    /* RTC fast memory (executable). Persists over deep sleep. */
    RTC_FAST : ORIGIN = 0x50000000, LENGTH = 0x4000
}

/* C6 maps code and rodata into one flash window: ROTEXT and RODATA share ROM. */
REGION_ALIAS("ROTEXT", ROM);
REGION_ALIAS("RODATA", ROM);

/* C6 has a single HP RAM region used for both code and data. */
REGION_ALIAS("RWDATA", RAM);
REGION_ALIAS("RWTEXT", RAM);

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

    _rwtext_len = . - ORIGIN(RWTEXT);
  } > RWTEXT

  /* No .rwdata_dummy here: on C3, IRAM and DRAM are two vaddr mappings of the
     same physical RAM, so a dummy was needed to keep .rwtext (IRAM) and .data
     (DRAM) from colliding. On C6 RWTEXT and RWDATA are the same region placed
     sequentially, so no dummy is required. */

  .sdata : ALIGN(4)
  {
    _sdata_start = ABSOLUTE(.);
    *(.sdata .sdata.* .sdata2 .sdata2.*);
    _sdata_end = ABSOLUTE(.);
    . = ALIGN(4);
  } > RWDATA

  .data : ALIGN(4)
  {
    _data_start = ABSOLUTE(.);
    . = ALIGN (4);

    *(.rodata.*_esp_hal_internal_handler*)
    *(.rodata..Lswitch.table.*)
    *(.rodata.cst*)

    *(.data .data.*);
    *(.data1)
    _data_end = ABSOLUTE(.);
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
    . = ORIGIN(RAM) + LENGTH(RAM) - 0x6000;
    __heap_end = .;
  } > RWDATA

  .stack (NOLOAD) : {
    . = ALIGN(16);
    __sys_stack_start = .;
    . += 0x6000;
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

PROVIDE(__global_pointer$ = ALIGN(_sdata_start, 4) + 0x800);

/* ---- libnet80211 / libwpa_supplicant 闭源 .a 引用的符号别名 ----
 * C3 的 link.x(seeed_xiao_esp32c3/link.x:305-321)把 .a 要的 g_* / WIFI_EVENT
 * 别名到 BlueOS 自实现的 __ESP_RADIO_* 符号,并 EXTERN 强制保留两个 mesh 符号。
 * C6 的 ROM .ld 不提供这些符号(与 C3 不同:C3 的 esp32c3.rom.ld 直接强定义了
 * g_misc_nvs/g_osi_funcs_p 等 ROM 地址,C6 ROM 只有 g_osi_funcs_p),故 C6 必须由
 * 本 link.x 自行 PROVIDE,否则链接报 undefined reference to `g_misc_nvs` / `WIFI_EVENT`
 * / `g_wifi_osi_funcs` / `g_log_level` 等。
 *   __ESP_RADIO_G_WIFI_OSI_FUNCS   -> kernel/src/net/link/esp32_wlan/mod.rs
 *   __ESP_RADIO_G_WIFI_FEATURE_CAPS-> kernel/src/net/link/esp32_wlan/mod.rs
 *   __ESP_RADIO_WIFI_EVENT         -> kernel/src/net/link/esp32_wlan/api.rs:42
 *   __ESP_RADIO_G_LOG_LEVEL        -> kernel/src/net/link/esp32_wlan/mod.rs (BlueOS 自补)
 *   __ESP_RADIO_G_MISC_NVS         -> kernel/src/net/link/esp32_wlan/mod.rs (BlueOS 自补)
 * g_espnow_user_oui / mesh_sta_auth_expire_time 无 Rust 定义,EXTERN 仅防止被
 * --gc-sections 丢弃(保留给未来 mesh/espnow 实现占位,弱引用不报错)。
 */
EXTERN( __ESP_RADIO_G_WIFI_OSI_FUNCS );
EXTERN( __ESP_RADIO_G_WIFI_FEATURE_CAPS );

PROVIDE( g_wifi_osi_funcs = __ESP_RADIO_G_WIFI_OSI_FUNCS );
PROVIDE( g_wifi_feature_caps = __ESP_RADIO_G_WIFI_FEATURE_CAPS );

EXTERN( __ESP_RADIO_WIFI_EVENT );
PROVIDE( WIFI_EVENT = __ESP_RADIO_WIFI_EVENT );

EXTERN( __ESP_RADIO_G_MISC_NVS );
EXTERN( __ESP_RADIO_G_LOG_LEVEL );
PROVIDE( g_misc_nvs = __ESP_RADIO_G_MISC_NVS );
PROVIDE( g_log_level = __ESP_RADIO_G_LOG_LEVEL );

EXTERN( g_espnow_user_oui );
EXTERN( mesh_sta_auth_expire_time );
