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
use alloc::vec::Vec;
use blueos_loader as loader;
use librs::pthread;
use semihosting::{io::Read, println};

fn read_all(ptr: *const core::ffi::c_char) -> semihosting::io::Result<Vec<u8>> {
    let path = unsafe { core::ffi::CStr::from_ptr(ptr) };
    let mut file = semihosting::fs::File::open(path)?;
    let mut tmp = [0u8; 64];
    let mut buf = Vec::new();
    loop {
        let size = file.read(&mut tmp)?;
        if size == 0 {
            break;
        }
        buf.extend_from_slice(&tmp[..size]);
    }
    Ok(buf)
}

#[cfg(not(soc_esp32c3))]
mod test_pic {
    use super::*;
    use blueos_test_macro::test;
    use core::ffi::c_char;

    extern "C" {
        static PIC_ELF_PATH: *const c_char;
        static INVALID_MAGIC_ELF_PATH: *const c_char;
        static INVALID_ENTRY_ELF_PATH: *const c_char;
        static INVALID_SEGMENT_SIZE_ELF_PATH: *const c_char;
    }

    // FIXME: The ELF file is too large in debug mode. We should use
    // lseek to parse the ELF file.
    #[cfg(not(debug_assertions))]
    #[test]
    pub fn test_load_elf_and_run() {
        let res = read_all(unsafe { PIC_ELF_PATH });
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

#[cfg(soc_esp32c3)]
mod test_exec {
    use super::*;
    use blueos_test_macro::test;
    use core::ffi::c_char;

    const RTC_FAST_START: usize = 0x5000_0000;
    const RTC_FAST_END: usize = 0x5000_2000;
    const EXPECTED_RESULT: u32 = 0x9afc_e987;

    static EXEC_REGIONS: [loader::MemoryRegion; 1] = [unsafe {
        loader::MemoryRegion::new(
            RTC_FAST_START,
            RTC_FAST_END,
            loader::MemoryPermissions::READ
                .bitor(loader::MemoryPermissions::WRITE)
                .bitor(loader::MemoryPermissions::EXECUTE),
        )
    }];

    static SHORT_REGIONS: [loader::MemoryRegion; 1] = [unsafe {
        // SAFETY: This is a valid subset of the reserved RTC-fast test range.
        loader::MemoryRegion::new(
            RTC_FAST_START,
            RTC_FAST_START + 16,
            loader::MemoryPermissions::READ
                .bitor(loader::MemoryPermissions::WRITE)
                .bitor(loader::MemoryPermissions::EXECUTE),
        )
    }];

    static NON_EXEC_REGIONS: [loader::MemoryRegion; 1] = [unsafe {
        // SAFETY: RTC-fast supports the advertised read and write accesses.
        loader::MemoryRegion::new(
            RTC_FAST_START,
            RTC_FAST_END,
            loader::MemoryPermissions::READ.bitor(loader::MemoryPermissions::WRITE),
        )
    }];

    extern "C" {
        static EXEC_ELF_PATH: *const c_char;
    }

    #[test]
    fn test_load_exec_elf_and_run() {
        let buf = read_all(unsafe { EXEC_ELF_PATH }).unwrap();
        let mut mapper = loader::MemoryMapper::new_fixed(&EXEC_REGIONS);
        assert!(loader::load_elf(&buf, &mut mapper).is_ok());
        let entry = mapper.real_entry().unwrap();
        let run = unsafe { core::mem::transmute::<usize, extern "C" fn() -> u32>(entry) };
        assert_eq!(run(), EXPECTED_RESULT);
    }

    #[test]
    fn test_exec_rejects_allocated_mapper() {
        let buf = read_all(unsafe { EXEC_ELF_PATH }).unwrap();
        let mut mapper = loader::MemoryMapper::new();
        assert!(loader::load_elf(&buf, &mut mapper).is_err());
    }

    #[test]
    fn test_exec_rejects_out_of_range_without_writing() {
        let buf = read_all(unsafe { EXEC_ELF_PATH }).unwrap();
        let before = unsafe { (RTC_FAST_START as *const u32).read_volatile() };
        let mut mapper = loader::MemoryMapper::new_fixed(&SHORT_REGIONS);
        assert!(loader::load_elf(&buf, &mut mapper).is_err());
        let after = unsafe { (RTC_FAST_START as *const u32).read_volatile() };
        assert_eq!(after, before);
    }

    #[test]
    fn test_exec_rejects_non_executable_region() {
        let buf = read_all(unsafe { EXEC_ELF_PATH }).unwrap();
        let mut mapper = loader::MemoryMapper::new_fixed(&NON_EXEC_REGIONS);
        assert!(loader::load_elf(&buf, &mut mapper).is_err());
    }

    #[test]
    fn test_exec_rejects_invalid_entry() {
        let mut buf = read_all(unsafe { EXEC_ELF_PATH }).unwrap();
        buf[24..28].copy_from_slice(&(RTC_FAST_END as u32).to_le_bytes());
        let mut mapper = loader::MemoryMapper::new_fixed(&EXEC_REGIONS);
        assert!(loader::load_elf(&buf, &mut mapper).is_err());
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
