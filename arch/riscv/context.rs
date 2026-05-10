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

// This context is used when we are performing context switching in thread mode
// or in the first level ISR. It is now owned by bluekernel_arch, but the layout
// is intentionally identical to the former kernel-side Context because saved_sp
// values are raw pointers into existing thread stacks.
#[cfg_attr(target_pointer_width = "64", repr(C, align(16)))]
#[cfg_attr(target_pointer_width = "32", repr(C, align(8)))]
#[derive(Default, Debug)]
pub struct Context {
    pub ra: usize,
    pub mepc: usize,
    pub gp: usize,
    pub tp: usize,
    pub t0: usize,
    pub t1: usize,
    pub t2: usize,
    pub fp: usize,
    pub a0: usize,
    pub a1: usize,
    pub a2: usize,
    pub a3: usize,
    pub a4: usize,
    pub a5: usize,
    pub a6: usize,
    pub a7: usize,
    pub t3: usize,
    pub t4: usize,
    pub t5: usize,
    pub t6: usize,
    pub s1: usize,
    pub s2: usize,
    pub s3: usize,
    pub s4: usize,
    pub s5: usize,
    pub s6: usize,
    pub s7: usize,
    pub s8: usize,
    pub s9: usize,
    pub s10: usize,
    pub s11: usize,
    // So that it is 16-byte aligned on RV64. Keep the field on RV32 too so
    // the existing assembly offsets and raw trap frame casts stay unchanged.
    pub padding: usize,
}

pub type TrapContext = Context;

#[repr(C, align(16))]
#[derive(Default, Debug)]
pub struct IsrContext {
    pub mstatus: usize,
    pub mcause: usize,
    pub mtval: usize,
    pub mepc: usize,
}

impl Context {
    #[inline]
    pub fn init(&mut self) -> &mut Self {
        self.gp = Self::__global_pointer();
        self
    }

    #[inline]
    pub fn __global_pointer() -> usize {
        let gp_val: usize;
        unsafe {
            core::arch::asm!("la {}, __global_pointer$", out(reg) gp_val,
                             options(nostack, nomem))
        }
        gp_val
    }

    // We are following C-ABI, since Rust ABI is not stabilized.
    // FIXME: rustc miscompiles it if inlined.
    #[inline(never)]
    pub fn set_return_address(&mut self, pc: usize) -> &mut Self {
        self.mepc = pc;
        self
    }

    #[inline(never)]
    pub fn set_arg(&mut self, index: usize, val: usize) -> &mut Self {
        match index {
            0 => self.a0 = val,
            1 => self.a1 = val,
            2 => self.a2 = val,
            3 => self.a3 = val,
            4 => self.a4 = val,
            5 => self.a5 = val,
            6 => self.a6 = val,
            7 => self.a7 = val,
            _ => {}
        }
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
