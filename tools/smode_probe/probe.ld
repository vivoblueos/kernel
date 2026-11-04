# Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Linker script for the S-mode feasibility probe.
#
# The layout mirrors the kernel's own (kernel/kernel/src/boards/*/link.x):
# the entry point goes first at 0x80000000, because QEMU's virt board with
# -bios none jumps to exactly that address - it does *not* honour the ELF
# entry point. Placing _start anywhere else means the machine executes
# whatever happens to sit at 0x80000000.
#
# Everything (code, rodata, bss) stays inside one contiguous 2 MiB window
# starting at the image base, because the probe identity-maps exactly that
# window and needs a single Sv39 leaf table to cover it.
#
# Note: lld only understands "#" comments in linker scripts.
#
# The `.text.init` / `.text` split is not cosmetic. QEMU's `virt` board with
# `-bios none` jumps to 0x80000000 and ignores the ELF entry point, so
# whatever sits at that address is what runs. If `putc` and the rest of the
# code shared one section, the section would start with `putc` instead of
# `_start`, and the machine would execute a character writer with a garbage
# stack - which looks like a mysterious hang, not like a linker mistake.
# `KEEP(*(.text.init))` therefore has to come *before* `*(.text .text.*)`.

OUTPUT_ARCH("riscv")
ENTRY(_start)

SECTIONS
{
    . = 0x80000000;

    .text : {
        . = ALIGN(16);
        KEEP(*(.text.init))
        *(.text .text.*)
        . = ALIGN(0x1000);
    }

    .rodata : {
        . = ALIGN(16);
        *(.srodata .srodata.*)
        *(.rodata .rodata.*)
    }

    .data : {
        . = ALIGN(16);
        *(.sdata .sdata.*)
        *(.data .data.*)
    }

    .bss : {
        . = ALIGN(16);
        __bss_start = .;
        *(.sbss .sbss.*)
        *(.bss .bss.*)
        __bss_end = .;
    }

    /DISCARD/ : {
        *(.comment)
        *(.note.*)
        *(.eh_frame.*)
    }
}
