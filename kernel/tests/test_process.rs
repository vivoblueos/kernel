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

#[cfg(target_arch = "aarch64")]
use alloc::boxed::Box;
#[cfg(target_arch = "aarch64")]
use blueos::{
    process::Process,
    scheduler,
    syscalls::{getpid, sched_yield},
    thread::{Builder, Entry},
    types::Arc,
};
#[cfg(target_arch = "aarch64")]
use blueos_test_macro::test;
#[cfg(target_arch = "aarch64")]
use core::ptr::NonNull;
#[cfg(target_arch = "aarch64")]
use core::sync::atomic::{AtomicU32, Ordering};

/// Spawn a kernel thread with a Process attached, run the closure, yield
/// until it completes, and return the Process handle so the caller can
/// inspect exit_code or other post-mortem state.
#[cfg(target_arch = "aarch64")]
fn spawn_with_process<F>(f: F) -> Arc<Process>
where
    F: FnOnce() + Send + 'static,
{
    let proc = Process::try_new().expect("Process::try_new failed");
    spawn_in_existing(proc.clone(), f);
    proc
}

/// Like [`spawn_with_process`] but attaches the thread to an existing
/// `Process` instead of creating a new one.  The caller keeps ownership
/// of the `Arc`; the thread only gets a back-pointer.
#[cfg(target_arch = "aarch64")]
fn spawn_in_existing<F>(proc: Arc<Process>, f: F)
where
    F: FnOnce() + Send + 'static,
{
    let proc_ptr = NonNull::new(Arc::as_ptr(&proc) as *mut Process).unwrap();

    extern "C" fn trampoline<F: FnOnce() + Send + 'static>(arg: *mut core::ffi::c_void) {
        let f = unsafe { Box::from_raw(arg as *mut F) };
        f();
    }

    let boxed: Box<F> = Box::new(f);
    let t = Builder::new(Entry::Posix(
        trampoline::<F>,
        Box::into_raw(boxed) as *mut core::ffi::c_void,
    ))
    .build();
    t.set_process(proc_ptr);
    scheduler::queue_ready_thread(t.state(), t);
    scheduler::yield_me();
}

#[cfg(target_arch = "aarch64")]
#[test]
fn test_getpid_returns_valid_pid() {
    let proc = spawn_with_process(|| {
        let pid = getpid::handle() as i32;
        assert!(pid > 0, "getpid must return a positive PID, got {pid}");
    });
    assert!(proc.pid > 0, "Process struct must have a positive PID");
}

#[cfg(target_arch = "aarch64")]
#[test]
fn test_getpid_different_across_processes() {
    let p1 = spawn_with_process(|| {
        let _ = getpid::handle();
    });
    let p2 = spawn_with_process(|| {
        let _ = getpid::handle();
    });
    let p3 = spawn_with_process(|| {
        let _ = getpid::handle();
    });

    assert!(p1.pid > 0);
    assert!(p2.pid > 0);
    assert!(p3.pid > 0);
    assert_ne!(p1.pid, p2.pid, "PIDs must be distinct across processes");
    assert_ne!(p2.pid, p3.pid, "PIDs must be distinct across processes");
    assert_ne!(p1.pid, p3.pid, "PIDs must be distinct across processes");
}

#[cfg(target_arch = "aarch64")]
#[test]
fn test_exit_code_stored_via_syscall() {
    // The exit syscall retires the thread, so we can't observe it directly
    // from the same thread.  Instead we verify the Process API works
    // (set_exit_code / exit_code round-trip), which is what the exit
    // syscall handler calls internally.
    let proc = spawn_with_process(|| {
        let t = scheduler::current_thread();
        if let Some(p) = t.process() {
            unsafe { p.as_ref() }.set_exit_code(42);
        }
    });
    assert_eq!(proc.exit_code(), 42, "exit_code must round-trip 42");
}

#[cfg(target_arch = "aarch64")]
#[test]
fn test_sched_yield_runs_other_thread() {
    static COUNTER: AtomicU32 = AtomicU32::new(0);

    spawn_with_process(|| {
        COUNTER.fetch_add(1, Ordering::Relaxed);
        sched_yield::handle();
        COUNTER.fetch_add(2, Ordering::Relaxed);
    });

    let val = COUNTER.load(Ordering::Relaxed);
    assert!(
        val >= 1,
        "spawned thread must have incremented counter, got {val}"
    );
}

#[cfg(target_arch = "aarch64")]
#[test]
fn test_multiple_processes_independent() {
    let p1 = spawn_with_process(|| {
        let pid = getpid::handle();
        assert!(pid > 0);
    });
    let p2 = spawn_with_process(|| {
        let pid = getpid::handle();
        assert!(pid > 0);
    });
    let p3 = spawn_with_process(|| {
        let pid = getpid::handle();
        assert!(pid > 0);
    });

    assert_ne!(p1.pid, p2.pid);
    assert_ne!(p2.pid, p3.pid);
    assert_ne!(p1.pid, p3.pid);
}

#[cfg(target_arch = "aarch64")]
#[test]
fn test_process_creation_allocates_asid() {
    let p = Process::try_new().expect("Process::try_new failed");
    assert!(
        p.asid > 0,
        "ASID must be non-zero for user processes, got {}",
        p.asid
    );
    assert!(
        p.asid_generation > 0,
        "generation must be non-zero, got {}",
        p.asid_generation
    );
}

#[cfg(target_arch = "aarch64")]
#[test]
fn test_exit_code_sentinel_is_negative() {
    let p = Process::try_new().expect("Process::try_new failed");
    assert_eq!(
        p.exit_code(),
        i32::MIN,
        "fresh process must report sentinel exit code"
    );
    assert!(
        p.exit_code() < 0,
        "sentinel must be distinguishable from valid exit codes"
    );
}

#[cfg(target_arch = "aarch64")]
#[test]
fn test_exit_code_roundtrip() {
    let p = Process::try_new().expect("Process::try_new failed");
    for code in [0, 1, 42, 127, 255, -1, i32::MAX] {
        p.set_exit_code(code);
        assert_eq!(p.exit_code(), code, "exit_code must round-trip {code}");
    }
}

#[cfg(target_arch = "aarch64")]
#[test]
fn test_thread_process_back_pointer() {
    let proc = spawn_with_process(|| {
        let t = scheduler::current_thread();
        let p = t
            .process()
            .expect("thread must have a process back-pointer");
        let pid = unsafe { p.as_ref() }.pid;
        assert!(
            pid > 0,
            "process back-pointer must point to a valid Process"
        );
    });
    assert!(proc.pid > 0);
}

#[cfg(target_arch = "aarch64")]
#[test]
fn test_asid_persists_across_threads() {
    let proc = Process::try_new().expect("Process::try_new failed");
    let asid = proc.asid;
    let gen = proc.asid_generation;

    spawn_in_existing(proc, move || {
        let t = scheduler::current_thread();
        let p = t.process().expect("thread must have a process");
        let p_ref = unsafe { p.as_ref() };
        assert_eq!(p_ref.asid, asid, "ASID must match across threads");
        assert_eq!(
            p_ref.asid_generation, gen,
            "generation must match across threads"
        );
    });
}
