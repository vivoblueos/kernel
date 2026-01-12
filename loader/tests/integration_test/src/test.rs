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
// Import it just for the global allocator.
use blueos_loader as loader;
use librs::pthread;
use semihosting::{io::Read, println};

mod test_everyting {
    use super::*;
    use alloc::vec::Vec;
    use blueos_test_macro::test;
    use core::ffi::c_char;
    use semihosting::io::Result;

    extern "C" {
        static EVERYTHING_ELF_PATH: *const c_char;
        static INVALID_MAGIC_ELF_PATH: *const c_char;
        static INVALID_ENTRY_ELF_PATH: *const c_char;
        static INVALID_SEGMENT_SIZE_ELF_PATH: *const c_char;
    }

    fn read_all(ptr: *const c_char) -> Result<Vec<u8>> {
        let path = unsafe { core::ffi::CStr::from_ptr(ptr) };
        let mut f = semihosting::fs::File::open(path)?;
        let mut tmp = [0u8; 64];
        let mut buf = alloc::vec::Vec::new();
        loop {
            let size = f.read(&mut tmp)?;
            if size == 0 {
                break;
            }
            buf.extend_from_slice(&tmp[0..size]);
        }
        Ok(buf)
    }

    // FIXME: The ELF file is too large in debug mode. We should use
    // lseek to parse the ELF file.
    #[cfg(not(debug_assertions))]
    #[test]
    pub fn test_load_elf_and_run() {
        let res = read_all(unsafe { EVERYTHING_ELF_PATH });
        assert!(res.is_ok());
        let buf = res.unwrap();
        let mut mapper = loader::MemoryMapper::new();
        let res = loader::load_elf(buf.as_slice(), &mut mapper);
        assert!(res.is_ok());
        let f = unsafe { core::mem::transmute::<usize, fn() -> ()>(mapper.real_entry().unwrap()) };
        f();
    }

    // FIXME: We should use FS's lseek API to get lower footprint.
    // TODO: Use semihosting's seek API to parse the ELF file.
    #[test]
    fn test_seek_and_parse_elf() {}

    #[cfg(not(debug_assertions))]
    #[test]
    fn test_invalid_entry() {
        let res = read_all(unsafe { INVALID_ENTRY_ELF_PATH });
        assert!(res.is_ok());
        let buf = res.unwrap();
        let mut mapper = loader::MemoryMapper::new();
        let res = loader::load_elf(buf.as_slice(), &mut mapper);
        assert!(res.is_err());
    }

    #[cfg(not(debug_assertions))]
    #[test]
    fn test_invalid_magic() {
        let res = read_all(unsafe { INVALID_MAGIC_ELF_PATH });
        assert!(res.is_ok());
        let buf = res.unwrap();
        let mut mapper = loader::MemoryMapper::new();
        let res = loader::load_elf(buf.as_slice(), &mut mapper);
        assert!(res.is_err());
    }

    #[cfg(not(debug_assertions))]
    #[test]
    fn test_invalid_segment_size() {
        let res = read_all(unsafe { INVALID_SEGMENT_SIZE_ELF_PATH });
        assert!(res.is_ok());
        let buf = res.unwrap();
        let mut mapper = loader::MemoryMapper::new();
        let res = loader::load_elf(buf.as_slice(), &mut mapper);
        assert!(res.is_err());
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
