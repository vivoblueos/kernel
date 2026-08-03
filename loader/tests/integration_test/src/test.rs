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
use core::ffi::c_char;
use librs::pthread;
use semihosting::{io::Read, println};

extern "C" {
    static LOADER_TEST_ELF_PATH: *const c_char;
    static INVALID_MAGIC_ELF_PATH: *const c_char;
    static INVALID_ENTRY_ELF_PATH: *const c_char;
    static INVALID_SEGMENT_SIZE_ELF_PATH: *const c_char;
}

#[cfg(loader_test_fixed_mapping)]
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

#[cfg(not(loader_test_fixed_mapping))]
mod test_pic {
    use super::*;
    use blueos_test_macro::test;

    // FIXME: The ELF file is too large in debug mode. We should use
    // lseek to parse the ELF file.
    #[cfg(not(debug_assertions))]
    #[test]
    pub fn test_load_elf_and_run() {
        let res = read_all(unsafe { LOADER_TEST_ELF_PATH });
        assert!(res.is_ok());
        let buf = res.unwrap();
        let mut mapper = loader::MemoryMapper::new(None);
        let res = loader::load_elf(buf.as_slice(), &mut mapper);
        assert!(res.is_ok());
        let f = unsafe { core::mem::transmute::<usize, fn() -> ()>(mapper.real_entry().unwrap()) };
        f();
    }

    // FIXME: We should use FS's lseek API to get lower footprint.
    // TODO: Use semihosting's seek API to parse the ELF file.
    #[test]
    fn test_seek_and_parse_elf() {}
}

mod test_malformed {
    #[cfg(loader_test_fixed_mapping)]
    use super::loader_test_config::TEST_REGIONS;
    use super::*;
    use blueos_test_macro::test;

    #[cfg(not(debug_assertions))]
    #[test]
    fn test_invalid_entry() {
        let res = read_all(unsafe { INVALID_ENTRY_ELF_PATH });
        assert!(res.is_ok());
        let buf = res.unwrap();
        #[cfg(loader_test_fixed_mapping)]
        let mut mapper = loader::MemoryMapper::new(Some(&TEST_REGIONS));
        #[cfg(not(loader_test_fixed_mapping))]
        let mut mapper = loader::MemoryMapper::new(None);
        let res = loader::load_elf(buf.as_slice(), &mut mapper);
        assert!(res.is_err());
    }

    #[cfg(not(debug_assertions))]
    #[test]
    fn test_invalid_magic() {
        let res = read_all(unsafe { INVALID_MAGIC_ELF_PATH });
        assert!(res.is_ok());
        let buf = res.unwrap();
        #[cfg(loader_test_fixed_mapping)]
        let mut mapper = loader::MemoryMapper::new(Some(&TEST_REGIONS));
        #[cfg(not(loader_test_fixed_mapping))]
        let mut mapper = loader::MemoryMapper::new(None);
        let res = loader::load_elf(buf.as_slice(), &mut mapper);
        assert!(res.is_err());
    }

    #[cfg(not(debug_assertions))]
    #[test]
    fn test_invalid_segment_size() {
        let res = read_all(unsafe { INVALID_SEGMENT_SIZE_ELF_PATH });
        assert!(res.is_ok());
        let buf = res.unwrap();
        #[cfg(loader_test_fixed_mapping)]
        let mut mapper = loader::MemoryMapper::new(Some(&TEST_REGIONS));
        #[cfg(not(loader_test_fixed_mapping))]
        let mut mapper = loader::MemoryMapper::new(None);
        let res = loader::load_elf(buf.as_slice(), &mut mapper);
        assert!(res.is_err());
    }
}

#[cfg(loader_test_fixed_mapping)]
mod test_exec {
    use super::{
        loader_test_config::{
            TEST_REGIONS, TEST_REGION_END, TEST_REGION_PERMISSIONS, TEST_REGION_START,
        },
        *,
    };
    use blueos_test_macro::test;

    const EXPECTED_RESULT: u32 = 0x9afc_e987;

    static SHORT_REGIONS: [loader::MemoryRegion; 1] = [unsafe {
        // SAFETY: This is a valid subset of the configured loader test range.
        loader::MemoryRegion::new(
            TEST_REGION_START,
            TEST_REGION_START + 16,
            TEST_REGION_PERMISSIONS,
        )
    }];

    static NON_EXEC_REGIONS: [loader::MemoryRegion; 1] = [unsafe {
        // SAFETY: The configured region supports read and write accesses.
        loader::MemoryRegion::new(
            TEST_REGION_START,
            TEST_REGION_END,
            loader::MemoryPermissions::READ.bitor(loader::MemoryPermissions::WRITE),
        )
    }];

    #[test]
    fn test_load_exec_elf_and_run() {
        let buf = read_all(unsafe { LOADER_TEST_ELF_PATH }).unwrap();
        let mut mapper = loader::MemoryMapper::new(Some(&TEST_REGIONS));
        assert!(loader::load_elf(&buf, &mut mapper).is_ok());
        let entry = mapper.real_entry().unwrap();
        let run = unsafe { core::mem::transmute::<usize, extern "C" fn() -> u32>(entry) };
        assert_eq!(run(), EXPECTED_RESULT);
    }

    #[test]
    fn test_exec_rejects_allocated_mapper() {
        let buf = read_all(unsafe { LOADER_TEST_ELF_PATH }).unwrap();
        let mut mapper = loader::MemoryMapper::new(None);
        assert!(loader::load_elf(&buf, &mut mapper).is_err());
    }

    #[test]
    fn test_exec_rejects_out_of_range_without_writing() {
        let buf = read_all(unsafe { LOADER_TEST_ELF_PATH }).unwrap();
        let before = unsafe { (TEST_REGION_START as *const u32).read_volatile() };
        let mut mapper = loader::MemoryMapper::new(Some(&SHORT_REGIONS));
        assert!(loader::load_elf(&buf, &mut mapper).is_err());
        let after = unsafe { (TEST_REGION_START as *const u32).read_volatile() };
        assert_eq!(after, before);
    }

    #[test]
    fn test_exec_rejects_non_executable_region() {
        let buf = read_all(unsafe { LOADER_TEST_ELF_PATH }).unwrap();
        let mut mapper = loader::MemoryMapper::new(Some(&NON_EXEC_REGIONS));
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
