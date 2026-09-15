// NEWLINE-TIMEOUT: 10
// ASSERT-SUCC: Loader integration test ended
// ASSERT-FAIL: Backtrace in Panic.*

#![no_main]
#![no_std]
#![feature(custom_test_frameworks)]
#![test_runner(loader_test_runner)]
#![reexport_test_harness_main = "loader_test_main"]
#![feature(c_size_t)]
#![feature(thread_local)]
#![feature(c_variadic)]

extern crate alloc;
extern crate rsrt;
use alloc::sync::Arc;
use blueos::{
    sync::{atomic_wait, atomic_wake, SpinLock},
    thread,
    time::Tick,
};
use blueos_loader as loader;
use blueos_loader::{ElfReader, LoadError, LoadErrorKind, LoadResult};
use core::{
    ffi::c_char,
    sync::atomic::{AtomicUsize, Ordering},
};
use librs::pthread;
use semihosting::{
    io::{Read, Seek, SeekFrom},
    println,
};

extern "C" {
    static LOADER_TEST_ELF_PATH: *const c_char;
    static INVALID_MAGIC_ELF_PATH: *const c_char;
    static INVALID_ENTRY_ELF_PATH: *const c_char;
    static INVALID_SEGMENT_SIZE_ELF_PATH: *const c_char;
}

#[cfg(loader_test_exec)]
mod loader_test_config {
    use blueos_loader as loader;

    const fn parse_hex(value: &str) -> usize {
        let bytes = value.as_bytes();
        if bytes.len() <= 2 || bytes[0] != b'0' || (bytes[1] != b'x' && bytes[1] != b'X') {
            panic!("loader test relocation value must be hexadecimal");
        }

        let mut index = 2;
        let mut result = 0usize;
        while index < bytes.len() {
            let digit = match bytes[index] {
                b'0'..=b'9' => (bytes[index] - b'0') as usize,
                b'a'..=b'f' => (bytes[index] - b'a' + 10) as usize,
                b'A'..=b'F' => (bytes[index] - b'A' + 10) as usize,
                _ => panic!("invalid loader test relocation hex value"),
            };
            result = result * 16 + digit;
            index += 1;
        }
        result
    }

    const fn parse_permissions(value: &str) -> loader::MemoryPermissions {
        let bytes = value.as_bytes();
        let mut index = 0;
        let mut permissions = loader::MemoryPermissions::NONE;
        while index < bytes.len() {
            let permission = match bytes[index] {
                b'r' => loader::MemoryPermissions::READ,
                b'w' => loader::MemoryPermissions::WRITE,
                b'x' => loader::MemoryPermissions::EXECUTE,
                _ => panic!("invalid loader test relocation permission"),
            };
            permissions = permissions.bitor(permission);
            index += 1;
        }
        permissions
    }

    pub const TEST_REGION_START: usize = parse_hex(env!("LOADER_TEST_RELOCATION_ORIGIN"));
    pub const TEST_REGION_END: usize =
        TEST_REGION_START + parse_hex(env!("LOADER_TEST_RELOCATION_LENGTH"));
    pub const TEST_REGION_PERMISSIONS: loader::MemoryPermissions =
        parse_permissions(env!("LOADER_TEST_RELOCATION_PERMISSIONS"));

    pub static TEST_REGIONS: [loader::MemoryRegion; 1] = [unsafe {
        loader::MemoryRegion::new(TEST_REGION_START, TEST_REGION_END, TEST_REGION_PERMISSIONS)
    }];
}

fn open_test_elf(ptr: *const core::ffi::c_char) -> semihosting::fs::File {
    let path = unsafe { core::ffi::CStr::from_ptr(ptr) };
    semihosting::fs::File::open(path).expect("open test ELF")
}

/// A seek-based `ElfReader` over a semihosting file: the image is never
/// buffered as a whole, so debug ELFs (with full debug info) load without
/// inflating the kernel heap.
struct SemihostingElfReader<'a> {
    file: &'a semihosting::fs::File,
    len: u64,
}

impl<'a> SemihostingElfReader<'a> {
    fn new(file: &'a semihosting::fs::File) -> semihosting::io::Result<Self> {
        let mut file = file;
        let len = file.seek(SeekFrom::End(0))?;
        file.seek(SeekFrom::Start(0))?;
        Ok(Self { file, len })
    }
}

fn io_error() -> LoadError {
    LoadError::new(LoadErrorKind::Io, loader::ErrorContext::None)
}

impl ElfReader for SemihostingElfReader<'_> {
    fn len(&self) -> LoadResult<u64> {
        Ok(self.len)
    }

    fn read_exact_at(&self, offset: u64, dst: &mut [u8]) -> LoadResult<()> {
        // `&File` implements Read/Seek, so a reborrow of the shared
        // reference is enough to move the file cursor.
        let mut file = self.file;
        file.seek(SeekFrom::Start(offset)).map_err(|_| io_error())?;
        let mut filled = 0;
        while filled < dst.len() {
            let n = file.read(&mut dst[filled..]).map_err(|_| io_error())?;
            if n == 0 {
                return Err(LoadError::new(
                    LoadErrorKind::OutOfBounds,
                    loader::ErrorContext::FileRange {
                        offset,
                        len: dst.len() as u64,
                        file_len: self.len,
                    },
                ));
            }
            filled += n;
        }
        Ok(())
    }
}

/// Stack used by each loader test while parsing or running an image.
///
/// Even a rejected ELF can traverse deep parser and mapping frames. On
/// riscv64 debug, running that path on the 12 KiB harness stack overwrites the
/// adjacent main-thread control block before the next test starts. The loaded
/// program also needs room for callbacks into `librs` (`malloc`, `Box`, `Vec`).
const RUN_STACK_SIZE: usize = 64 * 1024;

/// Run `body` on a stack this test owns, and return its value.
fn run_on_own_stack<F>(body: F) -> u32
where
    F: FnOnce() -> u32 + Send + 'static,
{
    let done = Arc::new(AtomicUsize::new(0));
    let placed = Arc::new(SpinLock::new(0u32));

    let (worker_done, worker_placed) = (done.clone(), placed.clone());
    thread::spawn_with_stack(RUN_STACK_SIZE, move || {
        *worker_placed.irqsave_lock() = body();
        worker_done.fetch_add(1, Ordering::Release);
        let _ = atomic_wake(&worker_done, usize::MAX);
    })
    .expect("spawn the stack that runs the loaded image");

    while done.load(Ordering::Acquire) == 0 {
        // A spurious return only re-reads the flag; the worker bumps it exactly
        // once and never resets it.
        let _ = atomic_wait(&done, 0, Tick::MAX);
    }
    // Bind before returning: as a tail expression the guard temporary would
    // outlive `placed`.
    let outcome = *placed.irqsave_lock();
    outcome
}

mod test_elf_loader {
    #[cfg(loader_test_exec)]
    use super::loader_test_config::{
        TEST_REGIONS, TEST_REGION_END, TEST_REGION_PERMISSIONS, TEST_REGION_START,
    };
    use super::*;
    use blueos_test_macro::test;

    #[cfg(loader_test_exec)]
    const EXPECTED_RESULT: u32 = 0x9afc_e987;

    #[cfg(loader_test_exec)]
    static SHORT_REGIONS: [loader::MemoryRegion; 1] = [unsafe {
        // SAFETY: This is a valid subset of the configured loader test range.
        loader::MemoryRegion::new(
            TEST_REGION_START,
            TEST_REGION_START + 16,
            TEST_REGION_PERMISSIONS,
        )
    }];

    #[cfg(loader_test_exec)]
    static NON_EXEC_REGIONS: [loader::MemoryRegion; 1] = [unsafe {
        // SAFETY: The configured region supports read and write accesses.
        loader::MemoryRegion::new(
            TEST_REGION_START,
            TEST_REGION_END,
            loader::MemoryPermissions::READ.bitor(loader::MemoryPermissions::WRITE),
        )
    }];

    fn new_mapper() -> loader::MemoryMapper {
        #[cfg(loader_test_exec)]
        {
            loader::MemoryMapper::new(Some(&TEST_REGIONS))
        }
        #[cfg(not(loader_test_exec))]
        {
            loader::MemoryMapper::new(None)
        }
    }

    fn assert_rejected_elf(path: *const c_char) {
        let path = path as usize;
        run_on_own_stack(move || {
            let file = open_test_elf(path as *const c_char);
            let reader = SemihostingElfReader::new(&file).unwrap();
            let mut mapper = new_mapper();
            assert!(loader::load_elf_from_reader(reader, &mut mapper).is_err());
            0
        });
    }

    #[test]
    fn test_load_elf_and_run() {
        let outcome = run_on_own_stack(|| {
            // The loaded program's malloc/Box/Vec path needs per-thread libc
            // state. Parsing rejected images does not, and registering every
            // short-lived worker would leave stale POSIX TCBs on non-ARM targets.
            pthread::register_my_posix_tcb();
            let file = open_test_elf(unsafe { LOADER_TEST_ELF_PATH });
            let reader = SemihostingElfReader::new(&file).unwrap();
            let mut mapper = new_mapper();
            assert!(loader::load_elf_from_reader(reader, &mut mapper).is_ok());

            let entry = mapper.real_entry().unwrap();

            #[cfg(all(loader_test_exec))]
            {
                let run = unsafe { core::mem::transmute::<usize, extern "C" fn() -> u32>(entry) };
                run()
            }
            #[cfg(not(loader_test_exec))]
            {
                let run = unsafe { core::mem::transmute::<usize, fn()>(entry) };
                run();
                0
            }
        });

        #[cfg(all(loader_test_exec))]
        assert_eq!(outcome, EXPECTED_RESULT);
        #[cfg(not(loader_test_exec))]
        let _ = outcome;
    }

    #[test]
    fn test_invalid_entry() {
        assert_rejected_elf(unsafe { INVALID_ENTRY_ELF_PATH });
    }

    #[test]
    fn test_invalid_magic() {
        assert_rejected_elf(unsafe { INVALID_MAGIC_ELF_PATH });
    }

    #[test]
    fn test_invalid_segment_size() {
        assert_rejected_elf(unsafe { INVALID_SEGMENT_SIZE_ELF_PATH });
    }

    #[cfg(loader_test_exec)]
    #[test]
    fn test_exec_rejects_allocated_mapper() {
        run_on_own_stack(|| {
            let file = open_test_elf(unsafe { LOADER_TEST_ELF_PATH });
            let reader = SemihostingElfReader::new(&file).unwrap();
            let mut mapper = loader::MemoryMapper::new(None);
            assert!(loader::load_elf_from_reader(reader, &mut mapper).is_err());
            0
        });
    }

    #[cfg(loader_test_exec)]
    #[test]
    fn test_exec_rejects_out_of_range_without_writing() {
        run_on_own_stack(|| {
            let file = open_test_elf(unsafe { LOADER_TEST_ELF_PATH });
            let reader = SemihostingElfReader::new(&file).unwrap();
            let before = unsafe { (TEST_REGION_START as *const u32).read_volatile() };
            let mut mapper = loader::MemoryMapper::new(Some(&SHORT_REGIONS));
            assert!(loader::load_elf_from_reader(reader, &mut mapper).is_err());
            let after = unsafe { (TEST_REGION_START as *const u32).read_volatile() };
            assert_eq!(after, before);
            0
        });
    }

    #[cfg(loader_test_exec)]
    #[test]
    fn test_exec_rejects_non_executable_region() {
        run_on_own_stack(|| {
            let file = open_test_elf(unsafe { LOADER_TEST_ELF_PATH });
            let reader = SemihostingElfReader::new(&file).unwrap();
            let mut mapper = loader::MemoryMapper::new(Some(&NON_EXEC_REGIONS));
            assert!(loader::load_elf_from_reader(reader, &mut mapper).is_err());
            0
        });
    }
}

#[no_mangle]
pub fn loader_test_runner(tests: &[&dyn Fn()]) {
    println!("Loader integration test started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Loader integration test ended");
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    pthread::register_my_posix_tcb();
    loader_test_main();
    #[cfg(coverage)]
    common_cov::write_coverage_data();
    0
}
