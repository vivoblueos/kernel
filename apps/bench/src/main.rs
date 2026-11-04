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

//! Measurement workload for the frozen baseline.
//!
//! Prints one `BENCH <name>=<value>` line per metric so the collector can parse
//! it without depending on human-readable formatting. Every measurement runs
//! inside the guest: host-side timing would measure QEMU, not the kernel.
//!
//! Timing goes through the raw `ClockGetTime` syscall instead of
//! `std::time::Instant`. The toolchain numbers `CLOCK_MONOTONIC` as 4 while the
//! kernel only accepts 0..=3, so `Instant::now()` panics with EINVAL on this
//! build; see the `clock_ids` note in report/baseline.json.

extern crate blueos_header;
extern crate blueos_scal;
extern crate libc;
extern crate librs;
extern crate rsrt;

use blueos_header::syscalls::NR::ClockGetTime;
use blueos_scal::bk_syscall;
use std::hint::black_box;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

/// Enough iterations to average out timer granularity, small enough that the
/// whole run stays well inside the 60s checker budget.
const SYSCALL_ITERS: u32 = 20_000;
const SWITCH_ITERS: u32 = 2_000;
const TCP_CHUNK: usize = 8 * 1024;
const TCP_CHUNKS: usize = 128;

/// Kernel `CLOCK_MONOTONIC`, as numbered by posix_timers.rs (not by the
/// toolchain headers, which use 4).
const KERNEL_CLOCK_MONOTONIC: u32 = 1;

/// One `clock_gettime` syscall. This is the measured operation itself: under
/// dsc it is a direct call into the handler, under swi it traps through `svc`.
/// The argument has to be `libc::timespec`: dsc passes it straight to the
/// handler, so a local repr(C) struct would not type-check.
fn kernel_clock_ns() -> i64 {
    let mut ts = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    unsafe {
        bk_syscall!(
            ClockGetTime,
            KERNEL_CLOCK_MONOTONIC,
            &mut ts as *mut libc::timespec
        );
    }
    ts.tv_sec as i64 * 1_000_000_000 + ts.tv_nsec as i64
}

fn main() {
    println!("BENCH-BEGIN");
    measure_syscall_roundtrip();
    measure_context_switch();
    measure_tcp_loopback();
    println!("BENCH-END");
}

fn measure_syscall_roundtrip() {
    let start = kernel_clock_ns();
    for _ in 0..SYSCALL_ITERS {
        black_box(kernel_clock_ns());
    }
    let elapsed = kernel_clock_ns() - start;
    let ns = if elapsed > 0 {
        elapsed as u64 / SYSCALL_ITERS as u64
    } else {
        0
    };
    println!(
        "BENCH syscall_roundtrip_ns={} iters={}",
        ns, SYSCALL_ITERS
    );
}

/// Two threads hand a mutex back and forth; each iteration costs two context
/// switches (wake the peer, block again), so the reported value is per switch.
fn measure_context_switch() {
    let pair = Arc::new((Mutex::new(0u8), Condvar::new()));
    let peer = Arc::clone(&pair);
    let worker = thread::spawn(move || {
        let (lock, cvar) = &*peer;
        loop {
            let mut turn = lock.lock().unwrap();
            while *turn == 0 {
                turn = cvar.wait(turn).unwrap();
            }
            if *turn == 2 {
                break;
            }
            *turn = 0;
            cvar.notify_one();
        }
    });

    let (lock, cvar) = &*pair;
    let start = kernel_clock_ns();
    for _ in 0..SWITCH_ITERS {
        let mut turn = lock.lock().unwrap();
        *turn = 1;
        cvar.notify_one();
        while *turn == 1 {
            turn = cvar.wait(turn).unwrap();
        }
    }
    let elapsed = kernel_clock_ns() - start;

    {
        let mut turn = lock.lock().unwrap();
        *turn = 2;
        cvar.notify_one();
    }
    let _ = worker.join();

    let ns = if elapsed > 0 {
        elapsed as u64 / (SWITCH_ITERS as u64 * 2)
    } else {
        0
    };
    println!("BENCH ctx_switch_ns={} iters={}", ns, SWITCH_ITERS * 2);
}

/// Loopback throughput through the in-kernel stack. Unavailable is reported as
/// a structured value rather than a panic: the baseline has to be collectable
/// even on a build where the loopback interface is not reachable.
fn measure_tcp_loopback() {
    const ADDR: &str = "127.0.0.1:18080";

    let listener = match TcpListener::bind(ADDR) {
        Ok(listener) => listener,
        Err(error) => {
            println!("BENCH tcp_loopback_mbps=unavailable reason=bind:{}", error);
            return;
        }
    };

    let server = thread::spawn(move || {
        let mut total = 0usize;
        if let Ok((mut stream, _)) = listener.accept() {
            let mut buf = [0u8; 1024];
            loop {
                match stream.read(&mut buf) {
                    Ok(0) | Err(_) => break,
                    Ok(n) => total += n,
                }
            }
        }
        total
    });

    let mut client = match TcpStream::connect(ADDR) {
        Ok(client) => client,
        Err(error) => {
            println!(
                "BENCH tcp_loopback_mbps=unavailable reason=connect:{}",
                error
            );
            return;
        }
    };

    let payload = [0xABu8; TCP_CHUNK];
    let start = kernel_clock_ns();
    let mut sent = 0usize;
    for _ in 0..TCP_CHUNKS {
        match client.write_all(&payload) {
            Ok(()) => sent += payload.len(),
            Err(_) => break,
        }
    }
    drop(client);
    let received = server.join().unwrap_or(0);
    let elapsed_ns = kernel_clock_ns() - start;

    if elapsed_ns <= 0 || sent == 0 {
        println!("BENCH tcp_loopback_mbps=unavailable reason=no_data");
        return;
    }
    let mbps = (sent as f64 * 8.0 / (elapsed_ns as f64 / 1e9)) / 1_000_000.0;
    println!(
        "BENCH tcp_loopback_mbps={:.3} sent={} recv={}",
        mbps, sent, received
    );
}
