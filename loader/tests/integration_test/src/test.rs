// NEWLINE-TIMEOUT: 5
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
use libc::{c_char, pthread_t};
use librs::pthread::{pthread_create, pthread_join};
use semihosting::{io::Read, println};

mod test_everyting {
    use super::*;
    use blueos_test_macro::test;

    extern "C" {
        static EVERYTHING_ELF_PATH: *const c_char;
    }

    // FIXME: The ELF file is too large in debug mode. We should use
    // lseek to parse the ELF file.
    #[cfg(not(debug_assertions))]
    #[test]
    pub fn test_load_elf_and_run() {
        let path =
            unsafe { core::ffi::CStr::from_ptr(EVERYTHING_ELF_PATH as *const core::ffi::c_char) };
        let mut f = semihosting::fs::File::open(path).unwrap();
        let mut tmp = [0u8; 64];
        let mut buf = alloc::vec::Vec::new();
        loop {
            let size = f.read(&mut tmp).unwrap();
            if size == 0 {
                break;
            }
            buf.extend_from_slice(&tmp[0..size]);
        }
        let mut mapper = loader::MemoryMapper::new();
        loader::load_elf(buf.as_slice(), &mut mapper).unwrap();
        let f = unsafe { core::mem::transmute::<usize, fn() -> ()>(mapper.real_entry().unwrap()) };
        f();
    }

    // FIXME: We should use FS's lseek API to get lower footprint.
    // TODO: Use semihosting's seek API to parse the ELF file.
    #[test]
    fn test_seek_and_parse_elf() {}
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

extern "C" fn posix_main(_: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    loader_test_main();
    core::ptr::null_mut()
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut t: pthread_t = 0;
    let rc = pthread_create(
        &mut t as *mut pthread_t,
        core::ptr::null(),
        posix_main,
        core::ptr::null_mut(),
    );
    assert_eq!(rc, 0);
    pthread_join(t, core::ptr::null_mut());

    #[cfg(coverage)]
    common_cov::write_coverage_data();

    0
}
