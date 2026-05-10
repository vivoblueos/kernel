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

use crate::ThreadContext;
use core::fmt;

// Phase 4 moves ownership of the AArch64 register-save layout into
// bluekernel_arch, but the exception entry code still treats saved stack
// pointers as raw TrapContext frames. Keep this struct byte-for-byte identical
// to the former kernel-side Context until the switch assembly and initial stack
// construction move over in later Phase 4 slices.
#[derive(Default, Debug)]
#[repr(C, align(16))]
pub struct Context {
    pub x0: usize,
    pub x1: usize,
    pub x2: usize,
    pub x3: usize,
    pub x4: usize,
    pub x5: usize,
    pub x6: usize,
    pub x7: usize,
    pub x8: usize,
    pub x9: usize,
    pub x10: usize,
    pub x11: usize,
    pub x12: usize,
    pub x13: usize,
    pub x14: usize,
    pub x15: usize,
    pub x16: usize,
    pub x17: usize,
    pub x18: usize,
    pub x19: usize,
    pub x20: usize,
    pub x21: usize,
    pub x22: usize,
    pub x23: usize,
    pub x24: usize,
    pub x25: usize,
    pub x26: usize,
    pub x27: usize,
    pub x28: usize,
    pub fp: usize, // x29
    pub lr: usize, // x30
    pub elr: usize,
    pub spsr: usize,
    pub padding: usize,
    pub v0: [u64; 2],
    pub v1: [u64; 2],
    pub v2: [u64; 2],
    pub v3: [u64; 2],
    pub v4: [u64; 2],
    pub v5: [u64; 2],
    pub v6: [u64; 2],
    pub v7: [u64; 2],
    pub v8: [u64; 2],
    pub v9: [u64; 2],
    pub v10: [u64; 2],
    pub v11: [u64; 2],
    pub v12: [u64; 2],
    pub v13: [u64; 2],
    pub v14: [u64; 2],
    pub v15: [u64; 2],
    pub v16: [u64; 2],
    pub v17: [u64; 2],
    pub v18: [u64; 2],
    pub v19: [u64; 2],
    pub v20: [u64; 2],
    pub v21: [u64; 2],
    pub v22: [u64; 2],
    pub v23: [u64; 2],
    pub v24: [u64; 2],
    pub v25: [u64; 2],
    pub v26: [u64; 2],
    pub v27: [u64; 2],
    pub v28: [u64; 2],
    pub v29: [u64; 2],
    pub v30: [u64; 2],
    pub v31: [u64; 2],
    pub fpcr: u64,
    pub fpsr: u64,
}

pub type TrapContext = Context;
pub type IsrContext = Context;

impl Context {
    #[inline]
    pub fn init(&mut self) -> &mut Self {
        self.spsr = 0b0101;
        self
    }

    // We are following C-ABI, since Rust ABI is not stabilized.
    // FIXME: rustc miscompiles it if inlined.
    #[inline(never)]
    pub fn set_return_address(&mut self, lr: usize) -> &mut Self {
        self.elr = lr;
        self
    }

    #[inline]
    pub fn set_arg(&mut self, index: usize, val: usize) -> &mut Self {
        match index {
            0 => self.x0 = val,
            1 => self.x1 = val,
            2 => self.x2 = val,
            3 => self.x3 = val,
            4 => self.x4 = val,
            5 => self.x5 = val,
            6 => self.x6 = val,
            7 => self.x7 = val,
            _ => {}
        }
        self
    }

    pub fn set_return_value(&mut self, val: usize) -> &mut Self {
        self.x0 = val;
        self
    }
}

impl ThreadContext for Context {
    fn init(&mut self) -> &mut Self {
        Self::init(self)
    }

    fn set_return_address(&mut self, address: usize) -> &mut Self {
        Self::set_return_address(self, address)
    }

    fn set_arg(&mut self, index: usize, value: usize) -> &mut Self {
        Self::set_arg(self, index, value)
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Context {{")?;
        write!(f, "x0: {:?}", self.x0)?;
        write!(f, "x1: {:?}", self.x1)?;
        write!(f, "x2: {:?}", self.x2)?;
        write!(f, "x3: {:?}", self.x3)?;
        write!(f, "x4: {:?}", self.x4)?;
        write!(f, "x5: {:?}", self.x5)?;
        write!(f, "x6: {:?}", self.x6)?;
        write!(f, "x7: {:?}", self.x7)?;
        write!(f, "x8: {:?}", self.x8)?;
        write!(f, "x9: {:?}", self.x9)?;
        write!(f, "x10: {:?}", self.x10)?;
        write!(f, "x11: {:?}", self.x11)?;
        write!(f, "x12: {:?}", self.x12)?;
        write!(f, "x13: {:?}", self.x13)?;
        write!(f, "x14: {:?}", self.x14)?;
        write!(f, "x15: {:?}", self.x15)?;
        write!(f, "x16: {:?}", self.x16)?;
        write!(f, "x17: {:?}", self.x17)?;
        write!(f, "x18: {:?}", self.x18)?;
        write!(f, "x19: {:?}", self.x19)?;
        write!(f, "x20: {:?}", self.x20)?;
        write!(f, "x21: {:?}", self.x21)?;
        write!(f, "x22: {:?}", self.x22)?;
        write!(f, "x23: {:?}", self.x23)?;
        write!(f, "x24: {:?}", self.x24)?;
        write!(f, "x25: {:?}", self.x25)?;
        write!(f, "x26: {:?}", self.x26)?;
        write!(f, "x27: {:?}", self.x27)?;
        write!(f, "x28: {:?}", self.x28)?;
        write!(f, "fp: {:?}", self.fp)?;
        write!(f, "lr: {:?}", self.lr)?;
        write!(f, "elr: {:?}", self.elr)?;
        write!(f, "spsr: {:?}", self.spsr)?;
        write!(f, "v0: {:?}", self.v0)?;
        write!(f, "v1: {:?}", self.v1)?;
        write!(f, "v2: {:?}", self.v2)?;
        write!(f, "v3: {:?}", self.v3)?;
        write!(f, "v4: {:?}", self.v4)?;
        write!(f, "v5: {:?}", self.v5)?;
        write!(f, "v6: {:?}", self.v6)?;
        write!(f, "v7: {:?}", self.v7)?;
        write!(f, "v8: {:?}", self.v8)?;
        write!(f, "v9: {:?}", self.v9)?;
        write!(f, "v10: {:?}", self.v10)?;
        write!(f, "v11: {:?}", self.v11)?;
        write!(f, "v12: {:?}", self.v12)?;
        write!(f, "v13: {:?}", self.v13)?;
        write!(f, "v14: {:?}", self.v14)?;
        write!(f, "v15: {:?}", self.v15)?;
        write!(f, "v16: {:?}", self.v16)?;
        write!(f, "v17: {:?}", self.v17)?;
        write!(f, "v18: {:?}", self.v18)?;
        write!(f, "v19: {:?}", self.v19)?;
        write!(f, "v20: {:?}", self.v20)?;
        write!(f, "v21: {:?}", self.v21)?;
        write!(f, "v22: {:?}", self.v22)?;
        write!(f, "v23: {:?}", self.v23)?;
        write!(f, "v24: {:?}", self.v24)?;
        write!(f, "v25: {:?}", self.v25)?;
        write!(f, "v26: {:?}", self.v26)?;
        write!(f, "v27: {:?}", self.v27)?;
        write!(f, "v28: {:?}", self.v28)?;
        write!(f, "v29: {:?}", self.v29)?;
        write!(f, "v30: {:?}", self.v30)?;
        write!(f, "v31: {:?}", self.v31)?;
        write!(f, "fpcr: {:?}", self.fpcr)?;
        write!(f, "fpsr: {:?}", self.fpsr)?;
        write!(f, "}}")
    }
}
