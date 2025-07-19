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

/// use bk_syscall! macro for convenience
/// syscall number same with https://github.com/qemu/qemu/blob/2fa4ad3f9000c385f71237984fdd1eefe2a91900/linux-user/arm/syscall.tbl#L14
pub const SYS_WRITE: i32 = 4;
pub const SYS_OPEN: i32 = 5;
pub const SYS_READ: i32 = 3;
pub const SYS_CLOSE: i32 = 6;
pub const SYS_LSEEK: i32 = 8;
pub const SYS_CHDIR: i32 = 12;
pub const SYS_CHMOD: i32 = 15;
pub const SYS_ACCESS: i32 = 33;
pub const SYS_SYNC: i32 = 36;
pub const SYS_FCHMOD: i32 = 94;
pub const SYS_FCNTL: i32 = 55;
pub const SYS_FDATASYNC: i32 = 148;
pub const SYS_NEWFSTATAT: i32 = 108;
pub const SYS_FSYNC: i32 = 118;
pub const SYS_FTRUNCATE: i32 = 93;
pub const SYS_FSTATFS: i32 = 100;
pub const SYS_FSTAT: i32 = 108;
pub const SYS_STATFS: i32 = 99;
pub const SYS_UNAME: i32 = 63;
pub const SYS_DUP: i32 = 41;
pub const SYS_RMDIR: i32 = 40;

pub const SYS_MMAP: i32 = 90;
pub const SYS_MUNMAP: i32 = 91;
pub const NANOSLEEP: i32 = 162;
pub const CLOCK_GETTIME: i32 = 263;
pub const CLOCK_GETRES: i32 = 264;
pub const CLOCK_SETTIME: i32 = 262;
pub const CLOCK_NANOSLEEP: i32 = 265;
pub const SYS_MKDIRAT: i32 = 323;
pub const SYS_MKNODAT: i32 = 324;
pub const SYS_RENAMEAT: i32 = 329;
pub const SYS_LINKAT: i32 = 330;
pub const SYS_PAUSE: i32 = 29;
pub const SYS_NICE: i32 = 34;
pub const SYS_UMASK: i32 = 60;
pub const SYS_SYMLINKAT: i32 = 331;
pub const SYS_UNLINKAT: i32 = 328;
pub const SYS_READLINKAT: i32 = 332;
pub const SYS_MQ_OPEN: i32 = 274;
pub const SYS_MQ_UNLINK: i32 = 275;
pub const SYS_MQ_GETSETATTR: i32 = 279;
pub const SYS_MQ_TIMEDSEND: i32 = 276;
pub const SYS_MQ_TIMEDRECEIVE: i32 = 277;
pub const SYS_SCHED_GET_PRIORITY_MAX: i32 = 159;
pub const SYS_SCHED_GET_PRIORITY_MIN: i32 = 160;
pub const SYS_SCHED_YIELD: i32 = 158;
pub const SYS_SCHED_RR_GET_INTERVAL: i32 = 161;
pub const SYS_PIPE2: i32 = 359;
pub const SYS_PREAD: i32 = 180;
pub const SYS_PWRITE: i32 = 181;
pub const SYS_GETDENTS: i32 = 141;
pub const SYS_GETCWD: i32 = 183;

pub const SYS_SOCKET: i32 = 281;
pub const SYS_BIND: i32 = 282;
pub const SYS_CONNECT: i32 = 283;
pub const SYS_LISTEN: i32 = 284;
pub const SYS_ACCEPT: i32 = 285;
pub const SYS_SEND: i32 = 289;
pub const SYS_SENDTO: i32 = 290;
pub const SYS_RECV: i32 = 291;
pub const SYS_RECVFROM: i32 = 292;
pub const SYS_SHUTDOWN: i32 = 293;
pub const SYS_SETSOCKOPT: i32 = 294;
pub const SYS_GETSOCKOPT: i32 = 295;
pub const SYS_SENDMSG: i32 = 296;
pub const SYS_RECVMSG: i32 = 297;

pub const SYS_GETADDRINFO: i32 = 298;
pub const SYS_FREEADDRINFO: i32 = 299;
