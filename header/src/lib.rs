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

#![no_std]

pub mod syscalls {
    //! BlueOS's syscall calling convention is compatible with Linux.
    // FIXME: We should really consider stable syscall nr.
    #[repr(usize)]
    #[derive(Copy, Clone)]
    pub enum NR {
        Nop,
        Echo,
        GetTid,
        CreateThread,
        ExitThread,
        AtomicWait,
        AtomicWake,
        ClockGetTime,
        AllocMem,
        FreeMem,
        Write,
        Close,
        Read,
        Open,
        Lseek,
        SchedYield,
        Fcntl,
        Mkdir,
        Rmdir,
        Stat,
        FStat,
        Statfs,
        FStatfs,
        Link,
        Unlink,
        Ftruncate,
        GetDents,
        Chdir,
        Getcwd,
        Mount,
        Umount,
        RtSigAction,
        SigAltStack,
        RtSigPending,
        RtSigProcmask,
        RtSigQueueInfo,
        RtSigSuspend,
        RtSigTimedWait,
        Socket,
        Bind,
        Connect,
        Listen,
        Accept,
        Send,
        Sendto,
        Recv,
        Recvfrom,
        Shutdown,
        Setsockopt,
        Getsockopt,
        Sendmsg,
        Recvmsg,
        GetAddrinfo,
        FreeAddrinfo,
        NanoSleep,
        LastNR,
    }
}

pub mod thread {
    #[cfg(debug)]
    pub const DEFAULT_STACK_SIZE: usize = 16384; // 16 kb
    #[cfg(release)]
    pub const DEFAULT_STACK_SIZE: usize = 12288; // 12 kb
    #[cfg(target_pointer_width = "32")]
    pub const STACK_ALIGN: usize = core::mem::size_of::<usize>();
    #[cfg(target_pointer_width = "64")]
    pub const STACK_ALIGN: usize = 16;

    #[repr(C)]
    pub struct SpawnArgs {
        pub spawn_hook: Option<fn(tid: usize, spawn_args: &SpawnArgs)>,
        pub entry: extern "C" fn(*mut core::ffi::c_void),
        pub arg: *mut core::ffi::c_void,
        pub stack_start: *mut u8,
        pub stack_size: usize,
    }

    #[repr(C)]
    #[derive(Clone, Debug)]
    pub struct ExitArgs {
        pub exit_hook: Option<fn(exit_args: &ExitArgs)>,
        pub tid: usize,
        pub stack_start: &'static u8,
    }
}
