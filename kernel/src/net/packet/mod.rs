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

//! Packet abstraction for the layered network architecture.
//!
//! Defines `Packet` and `PacketMeta` for the data path. Phase 0 only
//! defines the types — they are not yet integrated into the RX/TX path.
//!
//! # Phase 0
//!
//! These types are `#[allow(dead_code)]` and unused until Phase 1
//! (native L3 data path).

#![allow(dead_code)]

use alloc::vec::Vec;

/// Metadata associated with a network packet.
#[derive(Debug, Clone)]
pub struct PacketMeta {
    /// Index of the `NetIface` that received/sent this packet.
    pub iface_index: usize,
    /// IP protocol number (IANA: 6=TCP, 17=UDP, 1=ICMP).
    pub ip_proto: u8,
}

/// A network packet with metadata and buffer.
///
/// Provides header push/pop operations for building protocol layers.
/// `data_start` and `data_len` track the current protocol header boundary
/// within the buffer, allowing each layer to push/pop headers without
/// copying.
#[derive(Debug, Clone)]
pub struct Packet {
    /// Packet metadata.
    pub meta: PacketMeta,
    /// Backing buffer.
    buffer: Vec<u8>,
    /// Start offset of the current protocol data.
    data_start: usize,
    /// Length of the current protocol data.
    data_len: usize,
}

impl Packet {
    /// Create a new packet with the given buffer.
    pub fn new(meta: PacketMeta, buffer: Vec<u8>) -> Self {
        let data_len = buffer.len();
        Packet {
            meta,
            buffer,
            data_start: 0,
            data_len,
        }
    }

    /// Return the current data slice.
    pub fn data(&self) -> &[u8] {
        &self.buffer[self.data_start..self.data_start + self.data_len]
    }

    /// Return a mutable reference to the current data.
    pub fn data_mut(&mut self) -> &mut [u8] {
        &mut self.buffer[self.data_start..self.data_start + self.data_len]
    }

    /// Push a header of `len` bytes at the front, returning a mutable slice.
    pub fn push_header(&mut self, len: usize) -> &mut [u8] {
        assert!(self.data_start >= len);
        self.data_start -= len;
        self.data_len += len;
        &mut self.buffer[self.data_start..self.data_start + len]
    }

    /// Pop a header of `len` bytes from the front.
    pub fn pop_header(&mut self, len: usize) {
        assert!(self.data_len >= len);
        self.data_start += len;
        self.data_len -= len;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use blueos_test_macro::test;

    #[test]
    fn test_push_pop_header() {
        // Create with extra headroom so push_header works
        let meta = PacketMeta {
            iface_index: 0,
            ip_proto: 6,
        };
        let mut buf = vec![0u8; 8];
        buf[2..5].copy_from_slice(&[1, 2, 3]);
        // For now: set data at offset 2 so we can push a 2-byte header
        let mut pkt = Packet::new(meta, buf);
        // Manually offset data_start to simulate headroom
        // (Packet::new sets data_start=0; we adjust for test)
        pkt.data_start = 2;
        pkt.data_len = 3;
        assert_eq!(pkt.data(), &[1, 2, 3]);

        pkt.push_header(2);
        pkt.data_mut()[..2].copy_from_slice(&[0x45, 0x00]);
        assert_eq!(pkt.data(), &[0x45, 0x00, 1, 2, 3]);

        pkt.pop_header(2);
        assert_eq!(pkt.data(), &[1, 2, 3]);
    }
}