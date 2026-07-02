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

/// SPI peripheral trait — full-duplex transfer + half-duplex read/write
pub trait Spi<P, T>: super::PlatPeri + super::Configuration<P, Target = T> {
    /// Full-duplex transfer: simultaneously write `write` and read into `read`.
    ///
    /// Runs for `max(read.len(), write.len())` bytes. Overlapping/aliasing
    /// buffers is permitted (SPI hardware reads MISO and writes MOSI on
    /// separate lines simultaneously).
    fn transfer(&self, read: &mut [u8], write: &[u8]) -> super::err::Result<()>;

    /// Half-duplex read: read data into `buf` from the SPI slave.
    ///
    /// The word value sent on MOSI during reading is implementation-defined,
    /// typically `0x00` or `0xFF`.
    fn read(&self, buf: &mut [u8]) -> super::err::Result<()>;

    /// Half-duplex write: write data from `buf` to the SPI slave,
    /// discarding all incoming bytes on MISO.
    fn write(&self, buf: &[u8]) -> super::err::Result<()>;
}
