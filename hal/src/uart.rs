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

use crate::{
    err::{HalError, Result as HalResult},
    uart, Has8bitDataReg, HasFifo, HasInterruptReg, HasLineStatusReg, HasRestReg,
};

pub trait Uart<P, T, I, S>:
    super::PlatPeri
    + super::Configuration<P, Target = T>
    + HasInterruptReg<InterruptType = I>
    + HasFifo
    + Has8bitDataReg
    + HasLineStatusReg
{
    fn set_break_signal(&self, _enable: bool) -> HalResult<()> {
        Err(HalError::NotSupport)
    }
}

pub trait UartWithReset<P, T, I, S>:
    super::PlatPeri
    + super::Configuration<P, Target = T>
    + HasInterruptReg<InterruptType = I>
    + Has8bitDataReg
    + HasRestReg
{
    fn set_break_signal(&self, _enable: bool) -> HalResult<()> {
        Err(HalError::NotSupport)
    }
}
