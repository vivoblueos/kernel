// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// This code is copied from [esp-hal](https://github.com/esp-rs/esp-hal/blob/main/esp-bootloader-esp-idf/src/lib.rs)

// License: Apache-2.0 OR MIT
// Copyright 2021 esp-rs

/// ESP-IDF compatible application descriptor
///
/// This gets populated by the [esp_app_desc] macro.
#[repr(C)]
pub struct EspAppDesc {
    /// Magic word ESP_APP_DESC_MAGIC_WORD
    magic_word: u32,
    /// Secure version
    secure_version: u32,
    /// Reserved
    reserv1: [u32; 2],
    /// Application version
    version: [core::ffi::c_char; 32],
    /// Project name
    project_name: [core::ffi::c_char; 32],
    /// Compile time
    time: [core::ffi::c_char; 16],
    /// Compile date
    date: [core::ffi::c_char; 16],
    /// Version IDF
    idf_ver: [core::ffi::c_char; 32],
    /// sha256 of elf file
    app_elf_sha256: [u8; 32],
    /// Minimal eFuse block revision supported by image, in format: major * 100
    /// + minor
    min_efuse_blk_rev_full: u16,
    /// Maximal eFuse block revision supported by image, in format: major * 100
    /// + minor
    max_efuse_blk_rev_full: u16,
    /// MMU page size in log base 2 format
    mmu_page_size: u8,
    /// Reserved
    reserv3: [u8; 3],
    /// Reserved
    reserv2: [u32; 18],
}

#[unsafe(export_name = "esp_app_desc")]
#[unsafe(link_section = ".rodata_desc.appdesc")]
/// Application metadata descriptor.
/// FIXME: This is currently hardcoded, but we should generate it from build scripts.
pub static ESP_APP_DESC: EspAppDesc = EspAppDesc {
    magic_word: 0xABCD_5432,
    secure_version: 0,
    reserv1: [0; 2],
    version: str_to_cstr_array("0.1.0"),
    project_name: str_to_cstr_array("blueoskernel"),
    time: str_to_cstr_array("none"),
    date: str_to_cstr_array("none"),
    idf_ver: str_to_cstr_array("none"),
    app_elf_sha256: [0; 32],
    min_efuse_blk_rev_full: 0,
    max_efuse_blk_rev_full: 0xffff,
    mmu_page_size: 0x10,
    reserv3: [0; 3],
    reserv2: [0; 18],
};

const fn str_to_cstr_array<const C: usize>(s: &str) -> [::core::ffi::c_char; C] {
    let bytes = s.as_bytes();
    let mut ret: [::core::ffi::c_char; C] = [0; C];
    let mut i = 0;
    loop {
        ret[i] = bytes[i] as _;
        i += 1;
        if i >= bytes.len() || i >= C {
            break;
        }
    }
    ret
}
