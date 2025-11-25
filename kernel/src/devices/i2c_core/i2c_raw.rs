// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

use blueos_driver::i2c::I2cConfig;
use blueos_hal::PlatPeri;

pub struct BlockI2c<T: PlatPeri> {
    inner: &'static T,
}

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()> BlockI2c<T> {
    pub fn write_then_read(
        &mut self,
        addr: u16,
        write_buf: &[u8],
        read_buf: &mut [u8],
    ) -> blueos_hal::err::Result<()> {
        todo!()
    }
}
