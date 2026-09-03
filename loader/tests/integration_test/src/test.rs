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
    #[cfg(loader_test_flash)]
    static LOADER_TEST_USELIBRS_ELF_PATH: *const c_char;
    static INVALID_MAGIC_ELF_PATH: *const c_char;
    static INVALID_ENTRY_ELF_PATH: *const c_char;
    static INVALID_SEGMENT_SIZE_ELF_PATH: *const c_char;
}

#[cfg(loader_test_exec)]
mod loader_test_config {
    use blueos_loader as loader;
    #[cfg(loader_test_flash)]
    use {
        blueos::sync::SpinLock,
        core::sync::atomic::{AtomicUsize, Ordering},
        libc::{c_int, c_ulong, c_void, O_RDWR, SEEK_SET},
        librs::c_str::CStr,
        librs::esp32_flash::{
            EraseRangeRequest, MapExecRequest, ESP32_FLASH_ERASE_RANGE, ESP32_FLASH_MAP_EXEC,
            ESP32_FLASH_UNMAP, FLASH_IOCTL_ABI_VERSION,
        },
        librs::syscall::{Sys, Syscall},
    };

    pub(super) const fn parse_hex(value: &str) -> usize {
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

    pub(super) const fn parse_permissions(value: &str) -> loader::MemoryPermissions {
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

    #[cfg(loader_test_flash)]
    pub const FLASH_CAPACITY: usize = parse_hex(env!("LOADER_TEST_FLASH_CAPACITY"));

    pub const RAM_START: usize = parse_hex(env!("LOADER_TEST_RAM_ORIGIN"));
    pub const RAM_END: usize = RAM_START + parse_hex(env!("LOADER_TEST_RAM_LENGTH"));

    #[cfg(loader_test_flash)]
    pub const IROM_START: usize = parse_hex(env!("LOADER_TEST_IROM_ORIGIN"));
    #[cfg(loader_test_flash)]
    pub const IROM_END: usize = IROM_START + parse_hex(env!("LOADER_TEST_IROM_LENGTH"));
    #[cfg(loader_test_flash)]
    pub const IROM_FLASH_OFFSET: usize = parse_hex(env!("LOADER_TEST_IROM_FLASH_OFFSET"));

    #[cfg(loader_test_flash)]
    pub const RODATA_START: usize = parse_hex(env!("LOADER_TEST_RODATA_ORIGIN"));
    #[cfg(loader_test_flash)]
    pub const RODATA_END: usize = RODATA_START + parse_hex(env!("LOADER_TEST_RODATA_LENGTH"));
    #[cfg(loader_test_flash)]
    pub const RODATA_FLASH_OFFSET: usize = parse_hex(env!("LOADER_TEST_RODATA_FLASH_OFFSET"));

    #[cfg(loader_test_flash)]
    pub const RWDATA_START: usize = parse_hex(env!("LOADER_TEST_RWDATA_ORIGIN"));
    #[cfg(loader_test_flash)]
    pub const RWDATA_END: usize = RWDATA_START + parse_hex(env!("LOADER_TEST_RWDATA_LENGTH"));

    #[cfg(loader_test_flash)]
    static IROM_WRITTEN: AtomicUsize = AtomicUsize::new(0);
    #[cfg(loader_test_flash)]
    static RODATA_WRITTEN: AtomicUsize = AtomicUsize::new(0);
    #[cfg(loader_test_flash)]
    static FLASH_FD: SpinLock<Option<c_int>> = SpinLock::new(None);

    #[cfg(loader_test_flash)]
    fn flash_ioctl(request: u32, arg: usize) -> loader::Result {
        let fd = {
            let guard = FLASH_FD.lock();
            *guard.as_ref().ok_or("Flash device is not initialized")?
        };
        unsafe {
            Sys::ioctl(fd, request as c_ulong, arg as *mut c_void)
                .map(|_| ())
                .map_err(|_| "Flash ioctl failed")
        }
    }

    #[cfg(loader_test_flash)]
    pub fn init_flash_device() -> loader::Result {
        if FLASH_FD.lock().is_some() {
            return Err("Flash device is already initialized");
        }
        let path = unsafe { CStr::from_bytes_with_nul_unchecked(b"/dev/esp32-flash0\0") };
        let opened = Sys::open(path, O_RDWR, 0);
        if opened < 0 {
            return Err("Failed to open flash device");
        }
        *FLASH_FD.lock() = Some(opened);
        IROM_WRITTEN.store(0, Ordering::Relaxed);
        RODATA_WRITTEN.store(0, Ordering::Relaxed);
        Ok(())
    }

    #[cfg(loader_test_flash)]
    pub fn map_written_flash(require_rodata: bool) -> loader::Result {
        let irom_written = IROM_WRITTEN.load(Ordering::Relaxed);
        let rodata_written = RODATA_WRITTEN.load(Ordering::Relaxed);
        if irom_written == 0 || (require_rodata && rodata_written == 0) {
            return Err("Expected flash-backed ELF segments were not written");
        }

        let map_start = IROM_FLASH_OFFSET;
        let map_end = core::cmp::max(
            IROM_FLASH_OFFSET + irom_written,
            RODATA_FLASH_OFFSET + rodata_written,
        );
        let mut request = MapExecRequest {
            version: FLASH_IOCTL_ABI_VERSION,
            size: core::mem::size_of::<MapExecRequest>() as u32,
            flags: 0,
            region_offset: map_start as u32,
            image_size: (map_end - map_start) as u32,
            mapped_address: 0,
        };
        flash_ioctl(
            ESP32_FLASH_MAP_EXEC,
            &mut request as *mut MapExecRequest as usize,
        )?;
        if request.mapped_address as usize != IROM_START {
            let _ = flash_ioctl(ESP32_FLASH_UNMAP, 0);
            return Err("Flash driver returned an unexpected XIP address");
        }
        Ok(())
    }

    #[cfg(loader_test_flash)]
    pub fn unmap_flash() -> loader::Result {
        flash_ioctl(ESP32_FLASH_UNMAP, 0)?;
        let fd = FLASH_FD
            .lock()
            .take()
            .ok_or("Flash device is not initialized")?;
        Sys::close(fd).map_err(|_| "Failed to close flash device")
    }

    #[cfg(loader_test_flash)]
    fn write_flash(offset: usize, mut data: &[u8]) -> loader::Result {
        const FLASH_SECTOR_SIZE: usize = 4096;

        if data.is_empty() {
            return Ok(());
        }
        let erase_start = offset & !(FLASH_SECTOR_SIZE - 1);
        let erase_end = offset
            .checked_add(data.len())
            .and_then(|end| end.checked_add(FLASH_SECTOR_SIZE - 1))
            .map(|end| end & !(FLASH_SECTOR_SIZE - 1))
            .ok_or("Flash erase range overflow")?;
        let mut request = EraseRangeRequest {
            version: FLASH_IOCTL_ABI_VERSION,
            size: core::mem::size_of::<EraseRangeRequest>() as u32,
            flags: 0,
            region_offset: erase_start as u32,
            length: (erase_end - erase_start) as u32,
        };
        flash_ioctl(
            ESP32_FLASH_ERASE_RANGE,
            &mut request as *mut EraseRangeRequest as usize,
        )?;
        let fd = {
            let guard = FLASH_FD.lock();
            *guard.as_ref().ok_or("Flash device is not initialized")?
        };
        let mut write_offset = offset;
        while !data.is_empty() {
            let position = Sys::lseek(fd, write_offset as _, SEEK_SET);
            if position < 0 {
                return Err("Failed to seek flash device");
            }
            let written = Sys::write(fd, data).map_err(|_| "Failed to write flash device")?;
            if written == 0 {
                return Err("Flash device write made no progress");
            }
            write_offset += written;
            data = &data[written..];
        }
        Ok(())
    }

    #[cfg(loader_test_flash)]
    pub fn write_load_data(
        mapper: &mut loader::MemoryMapper,
        vaddr: usize,
        data: &[u8],
    ) -> loader::Result {
        let (region_start, flash_offset, written) = if (IROM_START..IROM_END).contains(&vaddr) {
            (IROM_START, IROM_FLASH_OFFSET, &IROM_WRITTEN)
        } else if (RODATA_START..RODATA_END).contains(&vaddr) {
            (RODATA_START, RODATA_FLASH_OFFSET, &RODATA_WRITTEN)
        } else {
            mapper.write_slice_at(vaddr, data)?;
            return Ok(());
        };
        let offset = vaddr
            .checked_sub(region_start)
            .and_then(|value| flash_offset.checked_add(value))
            .ok_or("Flash destination overflow")?;
        let end = offset
            .checked_add(data.len())
            .ok_or("Flash destination overflow")?;
        if end > FLASH_CAPACITY {
            return Err("Flash destination exceeds capacity");
        }
        write_flash(offset, data)?;
        written.fetch_max(vaddr - region_start + data.len(), Ordering::Relaxed);
        Ok(())
    }

    #[cfg(not(loader_test_flash))]
    pub static TEST_REGIONS: [loader::MemoryRegion; 1] = [unsafe {
        loader::MemoryRegion::new(
            RAM_START,
            RAM_END,
            parse_permissions(env!("LOADER_TEST_RAM_PERMISSIONS")),
        )
    }];

    #[cfg(loader_test_flash)]
    pub static TEST_REGIONS: [loader::MemoryRegion; 4] = [
        unsafe {
            loader::MemoryRegion::new(
                RAM_START,
                RAM_END,
                parse_permissions(env!("LOADER_TEST_RAM_PERMISSIONS")),
            )
        },
        unsafe {
            loader::MemoryRegion::new(
                IROM_START,
                IROM_END,
                parse_permissions(env!("LOADER_TEST_IROM_PERMISSIONS")),
            )
        },
        unsafe {
            loader::MemoryRegion::new(
                RODATA_START,
                RODATA_END,
                parse_permissions(env!("LOADER_TEST_RODATA_PERMISSIONS")),
            )
        },
        unsafe {
            loader::MemoryRegion::new(
                RWDATA_START,
                RWDATA_END,
                parse_permissions(env!("LOADER_TEST_RWDATA_PERMISSIONS")),
            )
        },
    ];

    #[cfg(not(loader_test_flash))]
    pub static NON_EXEC_REGIONS: [loader::MemoryRegion; 1] = [unsafe {
        loader::MemoryRegion::new(
            RAM_START,
            RAM_END,
            loader::MemoryPermissions::READ.bitor(loader::MemoryPermissions::WRITE),
        )
    }];

    #[cfg(loader_test_flash)]
    pub static NON_EXEC_REGIONS: [loader::MemoryRegion; 4] = [
        unsafe {
            loader::MemoryRegion::new(
                RAM_START,
                RAM_END,
                loader::MemoryPermissions::READ.bitor(loader::MemoryPermissions::WRITE),
            )
        },
        unsafe { loader::MemoryRegion::new(IROM_START, IROM_END, loader::MemoryPermissions::READ) },
        unsafe {
            loader::MemoryRegion::new(
                RODATA_START,
                RODATA_END,
                parse_permissions(env!("LOADER_TEST_RODATA_PERMISSIONS")),
            )
        },
        unsafe {
            loader::MemoryRegion::new(
                RWDATA_START,
                RWDATA_END,
                parse_permissions(env!("LOADER_TEST_RWDATA_PERMISSIONS")),
            )
        },
    ];
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

mod test_elf_loader {
    #[cfg(loader_test_flash)]
    use super::loader_test_config::{
        init_flash_device, map_written_flash, unmap_flash, write_load_data,
    };
    #[cfg(loader_test_exec)]
    use super::loader_test_config::{NON_EXEC_REGIONS, RAM_START, TEST_REGIONS};
    use super::*;
    use blueos_test_macro::test;

    #[cfg(loader_test_exec)]
    const EXPECTED_RESULT: u32 = 0x9afc_e987;

    #[cfg(loader_test_exec)]
    static SHORT_REGIONS: [loader::MemoryRegion; 1] = [unsafe {
        // SAFETY: This is a valid subset of the configured loader test range.
        loader::MemoryRegion::new(
            RAM_START,
            RAM_START + 16,
            loader::MemoryPermissions::READ
                .bitor(loader::MemoryPermissions::WRITE)
                .bitor(loader::MemoryPermissions::EXECUTE),
        )
    }];

    fn new_mapper() -> loader::MemoryMapper {
        #[cfg(loader_test_exec)]
        {
            loader::MemoryMapper::new(Some(&TEST_REGIONS), None)
        }
        #[cfg(not(loader_test_exec))]
        {
            loader::MemoryMapper::new(None, None)
        }
    }

    // FIXME: The PIC ELF file is too large in debug mode. We should use
    // lseek to parse the ELF file.
    #[cfg(not(debug_assertions))]
    #[test]
    fn test_load_elf_and_run() {
        let buf = read_all(unsafe { LOADER_TEST_ELF_PATH }).unwrap();
        let mut mapper = new_mapper();
        assert!(loader::load_elf(&buf, &mut mapper).is_ok());
        let entry = mapper.real_entry().unwrap();

        #[cfg(loader_test_exec)]
        {
            let run = unsafe { core::mem::transmute::<usize, extern "C" fn() -> u32>(entry) };
            assert_eq!(run(), EXPECTED_RESULT);
        }
        #[cfg(not(loader_test_exec))]
        {
            let run = unsafe { core::mem::transmute::<usize, fn()>(entry) };
            run();
        }
    }

    #[cfg(all(loader_test_flash, not(debug_assertions)))]
    #[test]
    fn test_load_uselibrs_and_run_from_flash() {
        let buf = read_all(unsafe { LOADER_TEST_USELIBRS_ELF_PATH }).unwrap();
        init_flash_device().unwrap();
        let mut mapper = loader::MemoryMapper::new(Some(&TEST_REGIONS), Some(write_load_data));
        assert!(loader::load_elf(&buf, &mut mapper).is_ok());
        map_written_flash(true).unwrap();
        let entry = mapper.real_entry().unwrap();
        let run = unsafe { core::mem::transmute::<usize, extern "C" fn() -> i32>(entry) };
        let result = run();
        unmap_flash().unwrap();
        assert_eq!(result, 0);
    }

    // FIXME: We should use FS's lseek API to get lower footprint.
    // TODO: Use semihosting's seek API to parse the ELF file.
    #[cfg(not(loader_test_exec))]
    #[test]
    fn test_seek_and_parse_elf() {}

    #[cfg(not(debug_assertions))]
    #[test]
    fn test_invalid_entry() {
        let res = read_all(unsafe { INVALID_ENTRY_ELF_PATH });
        assert!(res.is_ok());
        let buf = res.unwrap();
        let mut mapper = new_mapper();
        let res = loader::load_elf(buf.as_slice(), &mut mapper);
        assert!(res.is_err());
    }

    #[cfg(not(debug_assertions))]
    #[test]
    fn test_invalid_magic() {
        let res = read_all(unsafe { INVALID_MAGIC_ELF_PATH });
        assert!(res.is_ok());
        let buf = res.unwrap();
        let mut mapper = new_mapper();
        let res = loader::load_elf(buf.as_slice(), &mut mapper);
        assert!(res.is_err());
    }

    #[cfg(not(debug_assertions))]
    #[test]
    fn test_invalid_segment_size() {
        let res = read_all(unsafe { INVALID_SEGMENT_SIZE_ELF_PATH });
        assert!(res.is_ok());
        let buf = res.unwrap();
        let mut mapper = new_mapper();
        let res = loader::load_elf(buf.as_slice(), &mut mapper);
        assert!(res.is_err());
    }

    #[cfg(loader_test_exec)]
    #[test]
    fn test_exec_rejects_allocated_mapper() {
        let buf = read_all(unsafe { LOADER_TEST_ELF_PATH }).unwrap();
        let mut mapper = loader::MemoryMapper::new(None, None);
        assert!(loader::load_elf(&buf, &mut mapper).is_err());
    }

    #[cfg(loader_test_exec)]
    #[test]
    fn test_exec_rejects_out_of_range_without_writing() {
        let buf = read_all(unsafe { LOADER_TEST_ELF_PATH }).unwrap();
        let before = unsafe { (RAM_START as *const u32).read_volatile() };
        let mut mapper = loader::MemoryMapper::new(Some(&SHORT_REGIONS), None);
        assert!(loader::load_elf(&buf, &mut mapper).is_err());
        let after = unsafe { (RAM_START as *const u32).read_volatile() };
        assert_eq!(after, before);
    }

    #[cfg(loader_test_exec)]
    #[test]
    fn test_exec_rejects_non_executable_region() {
        let buf = read_all(unsafe { LOADER_TEST_ELF_PATH }).unwrap();
        let mut mapper = loader::MemoryMapper::new(Some(&NON_EXEC_REGIONS), None);
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
