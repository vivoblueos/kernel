/*
 * Linker script for a user image.
 *
 * The link address must match `user::USER_IMAGE_BASE` in the kernel; a
 * mismatch is caught by the loader (the ELF header's entry point would land
 * outside the mapped segment) rather than by a wild jump at run time.
 *
 * Every output section is page-aligned so that the program headers get
 * separate segments with separate permissions, which is what lets the loader
 * give `.text` RX and the rest RW. Without the alignment the linker merges
 * them into one RWX segment and the kernel's W^X check refuses the image.
 */
ENTRY(_start)

SECTIONS
{
    . = 0x00010000;

    .text : {
        *(.text.entry)
        *(.text .text.*)
    }

    . = ALIGN(0x1000);

    .rodata : {
        *(.rodata .rodata.*)
        *(.srodata .srodata.*)
    }

    . = ALIGN(0x1000);

    .data : {
        *(.data .data.*)
        *(.sdata .sdata.*)
    }

    .bss : {
        *(.sbss .sbss.*)
        *(.bss .bss.*)
        *(COMMON)
    }

    /* Nothing here is loadable, and the loader would otherwise have to decide
     * what to do with a segment it cannot map. */
    /DISCARD/ : {
        *(.comment)
        *(.riscv.attributes)
        *(.note .note.*)
        *(.eh_frame .eh_frame_hdr)
    }
}
