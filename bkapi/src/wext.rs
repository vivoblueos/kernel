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

use libc::{c_char, c_int, c_uint, c_ulong, c_void, sockaddr};

pub const IFNAMSIZ: usize = 16;

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct IwParam {
    pub value: i32,
    pub fixed: u8,
    pub disabled: u8,
    pub flags: u16,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct IwPoint {
    pub pointer: *mut c_void,
    pub length: u16,
    pub flags: u16,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct IwFreq {
    pub m: i32,
    pub e: i16,
    pub i: u8,
    pub flags: u8,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct IwQuality {
    pub qual: u8,
    pub level: u8,
    pub noise: u8,
    pub updated: u8,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Iwreq {
    pub ifr_ifrn: [c_char; IFNAMSIZ],
    pub u: IwreqData,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct IwScanReq {
    pub scan_type: u8,
    pub essid_len: u8,
    pub num_channels: u8,
    pub flags: u8,
    pub bssid: sockaddr,
    pub essid: [u8; IW_ESSID_MAX_SIZE],
    pub min_channel_time: u32,
    pub max_channel_time: u32,
    pub channel_list: [IwFreq; IW_MAX_FREQUENCIES],
}

#[repr(C)]
#[derive(Clone, Copy)]
pub union IwreqData {
    pub name: [c_char; IFNAMSIZ],
    pub nwid: IwParam,
    pub essid: IwPoint,
    pub freq: IwFreq,
    pub sens: IwParam,
    pub bitrate: IwParam,
    pub txpower: IwParam,
    pub rts: IwParam,
    pub frag: IwParam,
    pub mode: u32,
    pub retry: IwParam,
    pub encoding: IwPoint,
    pub power: IwParam,
    pub qual: IwQuality,
    pub ap_addr: sockaddr,
    pub addr: sockaddr,
    pub param: IwParam,
    pub data: IwPoint,
}

// Wireless ioctl constants
pub const SIOCSIWCOMMIT: c_ulong = 0x8B00;
pub const SIOCGIWNAME: c_ulong = 0x8B01;
pub const SIOCSIWNWID: c_ulong = 0x8B02;
pub const SIOCGIWNWID: c_ulong = 0x8B03;
pub const SIOCSIWFREQ: c_ulong = 0x8B04;
pub const SIOCGIWFREQ: c_ulong = 0x8B05;
pub const SIOCSIWMODE: c_ulong = 0x8B06;
pub const SIOCGIWMODE: c_ulong = 0x8B07;
pub const SIOCSIWSENS: c_ulong = 0x8B08;
pub const SIOCGIWSENS: c_ulong = 0x8B09;
pub const SIOCSIWAP: c_ulong = 0x8B14;
pub const SIOCGIWAP: c_ulong = 0x8B15;
pub const SIOCSIWMLME: c_ulong = 0x8B16;
pub const SIOCGIWMLME: c_ulong = 0x8B17;
pub const SIOCSIWSCAN: c_ulong = 0x8B18;
pub const SIOCGIWSCAN: c_ulong = 0x8B19;
pub const SIOCSIWESSID: c_ulong = 0x8B1A;
pub const SIOCGIWESSID: c_ulong = 0x8B1B;
pub const SIOCSIWENCODE: c_ulong = 0x8B2A;
pub const SIOCGIWENCODE: c_ulong = 0x8B2B;
pub const SIOCSIWAUTH: c_ulong = 0x8B32;
pub const SIOCGIWAUTH: c_ulong = 0x8B33;

// Wireless scan flags
pub const IW_SCAN_DEFAULT: c_uint = 0x0000;
pub const IW_SCAN_ALL_ESSID: c_uint = 0x0001;
pub const IW_SCAN_THIS_ESSID: c_uint = 0x0002;
pub const IW_SCAN_ALL_FREQ: c_uint = 0x0004;
pub const IW_SCAN_THIS_FREQ: c_uint = 0x0008;
pub const IW_SCAN_ALL_MODE: c_uint = 0x0010;
pub const IW_SCAN_THIS_MODE: c_uint = 0x0020;
pub const IW_SCAN_ALL_RATE: c_uint = 0x0040;
pub const IW_SCAN_THIS_RATE: c_uint = 0x0080;
pub const IW_SCAN_TYPE_ACTIVE: c_int = 0;
pub const IW_SCAN_TYPE_PASSIVE: c_int = 1;
pub const IW_SCAN_MAX_DATA: usize = 4096;

pub const IW_ESSID_MAX_SIZE: usize = 32;
pub const IW_MAX_FREQUENCIES: usize = 32;
