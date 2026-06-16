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

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EventPhase {
    Begin = 1,
    End = 2,
    Instant = 3,
    Counter = 4,
}

#[repr(u16)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EventId {
    TraceStart = 0x0001,
    TraceStop = 0x0002,
    TraceDropped = 0x0003,

    SchedSwitch = 0x0101,
    ThreadCreate = 0x0102,
    ThreadExit = 0x0103,
    ThreadWakeup = 0x0104,
    ThreadBlock = 0x0105,

    IrqEnter = 0x0201,
    IrqExit = 0x0202,

    SysEnter = 0x0301,
    SysExit = 0x0302,

    LockWaitBegin = 0x0401,
    LockWaitEnd = 0x0402,
    LockHoldBegin = 0x0403,
    LockHoldEnd = 0x0404,

    MmAlloc = 0x0501,
    MmFree = 0x0502,
    MmAllocFail = 0x0503,

    CounterMemUsedBytes = 0x0601,
}

#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct RecordHeader {
    pub ts_ns: u64,
    pub event_id: u16,
    pub cpu_id: u16,
    pub tid: u32,
    pub phase: u8,
    pub flags: u8,
    pub payload_len: u16,
}

#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct EventRecord {
    pub header: RecordHeader,
    pub data: [usize; 4],
}

impl EventRecord {
    pub const fn empty() -> Self {
        Self {
            header: RecordHeader {
                ts_ns: 0,
                event_id: 0,
                cpu_id: 0,
                tid: 0,
                phase: 0,
                flags: 0,
                payload_len: 0,
            },
            data: [0; 4],
        }
    }
}
