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
//
// This code is based on relibc (original license follows):
// https://github.com/redox-os/relibc/blob/master/LICENSE
// standard MIT license

#![allow(non_camel_case_types)]

use core::num::NonZeroU32;
use libc::{c_int, PTHREAD_PROCESS_PRIVATE};

#[derive(Clone, Copy)]
pub(crate) struct BarrierAttr {
    pub pshared: c_int,
}
impl Default for BarrierAttr {
    fn default() -> Self {
        // pshared = PTHREAD_PROCESS_PRIVATE is default according to POSIX.
        Self {
            pshared: PTHREAD_PROCESS_PRIVATE,
        }
    }
}

#[repr(C)]
pub struct Barrier {
    original_count: NonZeroU32,
    // 4
    lock: crate::sync::GenericMutex<Inner>,
    // 16
    cvar: crate::sync::cond::Cond,
    // 24
}
#[derive(Debug)]
struct Inner {
    count: u32,
    // TODO: Overflows might be problematic... 64-bit?
    gen_id: u32,
}

pub enum WaitResult {
    Waited,
    NotifiedAll,
}

impl Barrier {
    pub fn new(count: NonZeroU32) -> Self {
        Self {
            original_count: count,
            lock: crate::sync::GenericMutex::new(Inner {
                count: 0,
                gen_id: 0,
            }),
            cvar: crate::sync::cond::Cond::new(),
        }
    }
    pub fn wait(&self) -> WaitResult {
        let mut guard = self.lock.lock();
        let gen_id = guard.gen_id;

        guard.count += 1;

        if guard.count == self.original_count.get() {
            guard.gen_id = guard.gen_id.wrapping_add(1);
            guard.count = 0;

            let _ = self.cvar.broadcast();

            drop(guard);

            WaitResult::NotifiedAll
        } else {
            while guard.gen_id == gen_id {
                guard = self.cvar.wait_inner_typedmutex(guard);
            }

            WaitResult::Waited
        }
    }
}
