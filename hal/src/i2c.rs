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

pub trait I2c<P, T>:
    super::PlatPeri
    + super::Configuration<P, Target = T>
    + super::Has8bitDataReg
    + super::HasFifo
    + super::HasErrorStatusReg
{
    fn start_writing(&self, addr: u16) -> super::err::Result<()>;
    fn start_reading(&self, addr: u16) -> super::err::Result<()>;
    fn send_byte_with_stop(&self, byte: u8) -> super::err::Result<()>;
    fn read_byte_with_stop(&self) -> super::err::Result<u8>;
}
