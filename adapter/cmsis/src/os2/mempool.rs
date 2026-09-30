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

// The implementation is trying conforming to
// https://arm-software.github.io/CMSIS_6/main/RTOS2/group__CMSIS__RTOS__PoolMgmt.html.

use alloc::boxed::Box;
use blueos::{irq, support::Storage, time::Tick};
use blueos_adapter::mempool::MemoryPool;
use cmsis_os2::{
    osMemoryPoolAttr_t, osMemoryPoolId_t, osStatus_t, osStatus_t_osErrorISR,
    osStatus_t_osErrorParameter, osStatus_t_osErrorResource, osStatus_t_osOK,
};
use core::ffi::c_void;

#[no_mangle]
pub unsafe extern "C" fn osMemoryPoolNew(
    block_count: u32,
    block_size: u32,
    attr: *const osMemoryPoolAttr_t,
) -> osMemoryPoolId_t {
    if irq::is_in_irq() {
        return core::ptr::null_mut();
    }
    // `block_count` and `block_size` arrive as C ABI u32 values and their
    // product sizes the caller's `mp_mem`. The old u32 multiplication could
    // wrap around (for example 2 * 0x8000_0000 == 0), letting an undersized
    // buffer pass the size check and handing out block pointers past its
    // end. Compute the product in u64 (two u32 factors cannot overflow u64)
    // and reject zero sized pools as well.
    if block_count == 0 || block_size == 0 {
        return core::ptr::null_mut();
    }
    let required_size = u64::from(block_count) * u64::from(block_size);
    let mut result = core::ptr::null_mut();
    let attr = if attr.is_null() { None } else { Some(&*attr) };
    let mut data = None;
    if let Some(attr) = attr {
        if !attr.mp_mem.is_null() {
            if u64::from(attr.mp_size) < required_size {
                return core::ptr::null_mut();
            }
            data = Some(core::slice::from_raw_parts_mut(
                attr.mp_mem as *mut u8,
                attr.mp_size as usize,
            ));
        }
        if attr.cb_mem.is_null() {
            result = Box::into_raw(Box::new(MemoryPool::new()));
        } else {
            if (attr.cb_size as usize) < core::mem::size_of::<MemoryPool>() {
                return core::ptr::null_mut();
            }
            result = attr.cb_mem as *mut MemoryPool;
            core::ptr::write_bytes(result, 0, 1);
        }
    } else {
        result = Box::into_raw(Box::new(MemoryPool::new()));
    }
    debug_assert_ne!(result, core::ptr::null_mut());
    let inner = &mut *result;
    inner.init(block_count as usize, block_size as usize, data);
    result as osMemoryPoolId_t
}

#[no_mangle]
pub unsafe extern "C" fn osMemoryPoolAlloc(
    mp_id: osMemoryPoolId_t,
    timeout: u32,
) -> *mut core::ffi::c_void {
    if irq::is_in_irq() && timeout != 0 {
        return core::ptr::null_mut();
    }
    if mp_id.is_null() {
        return core::ptr::null_mut();
    }
    let mp = &mut *(mp_id as *mut MemoryPool);
    mp.get_block_with_timeout(Tick(timeout as usize))
}

#[no_mangle]
pub unsafe extern "C" fn osMemoryPoolFree(
    mp_id: osMemoryPoolId_t,
    block: *mut core::ffi::c_void,
) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    if mp_id.is_null() || block.is_null() {
        return osStatus_t_osErrorParameter;
    }
    let mp = &mut *(mp_id as *mut MemoryPool);
    mp.put_block(block);
    osStatus_t_osOK
}

#[no_mangle]
pub unsafe extern "C" fn osMemoryPoolGetCapacity(mp_id: osMemoryPoolId_t) -> u32 {
    if mp_id.is_null() {
        return 0;
    }
    let mp = &mut *(mp_id as *mut MemoryPool);
    mp.total_blocks() as u32
}

#[no_mangle]
pub unsafe extern "C" fn osMemoryPoolGetBlockSize(mp_id: osMemoryPoolId_t) -> u32 {
    if mp_id.is_null() {
        return 0;
    }
    let mp = &mut *(mp_id as *mut MemoryPool);
    mp.block_size() as u32
}

#[no_mangle]
pub unsafe extern "C" fn osMemoryPoolGetCount(mp_id: osMemoryPoolId_t) -> u32 {
    if mp_id.is_null() {
        return 0;
    }
    let mp = &mut *(mp_id as *mut MemoryPool);
    (mp.total_blocks() - mp.free_blocks()) as u32
}

#[no_mangle]
pub unsafe extern "C" fn osMemoryPoolGetSpace(mp_id: osMemoryPoolId_t) -> u32 {
    if irq::is_in_irq() {
        return 0;
    }
    if mp_id.is_null() {
        return 0;
    }
    let mp = &mut *(mp_id as *mut MemoryPool);
    mp.free_blocks() as u32
}

#[no_mangle]
pub unsafe extern "C" fn osMemoryPoolDelete(mp_id: osMemoryPoolId_t) -> osStatus_t {
    // FIXME: Check osErrorSafetyClass condition.
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    let ptr = mp_id as *mut MemoryPool;
    if ptr.is_null() {
        return osStatus_t_osErrorParameter;
    }
    let mp = &mut *ptr;
    if mp.total_blocks() != mp.free_blocks() {
        return osStatus_t_osErrorResource;
    }
    mp.clear();
    drop(Box::from_raw(ptr));
    osStatus_t_osOK
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;
    use core::alloc::Layout;

    #[test]
    fn test_c_mempool_basic() {
        unsafe {
            let mp_id = osMemoryPoolNew(4, 512, core::ptr::null());
            assert_eq!(osMemoryPoolGetBlockSize(mp_id), 512);
            assert_eq!(osMemoryPoolGetCapacity(mp_id), 4);
            assert_eq!(osMemoryPoolGetCount(mp_id), 0);
            assert_eq!(osMemoryPoolGetSpace(mp_id), 4);
            let block = osMemoryPoolAlloc(mp_id, 1024);
            assert!(!block.is_null());
            assert_eq!(osMemoryPoolDelete(mp_id), osStatus_t_osErrorResource);
            assert_eq!(osMemoryPoolFree(mp_id, block), osStatus_t_osOK);
            assert_eq!(osMemoryPoolDelete(mp_id), osStatus_t_osOK);
        }
    }

    #[test]
    fn test_attribute() {
        let mut attr: osMemoryPoolAttr_t = unsafe { core::mem::zeroed() };
        let block_count = 16;
        let block_size = 64;
        let cb_layout = Layout::from_size_align(
            core::mem::size_of::<MemoryPool>(),
            core::mem::align_of::<MemoryPool>(),
        )
        .unwrap();
        let cb = Storage::from_layout(cb_layout);
        let data_layout = Layout::from_size_align(block_count * block_size, 8).unwrap();
        let data = Storage::from_layout(cb_layout);
        attr.cb_mem = cb.base() as *mut c_void;
        attr.cb_size = cb_layout.size() as u32;
        attr.mp_mem = data.base() as *mut c_void;
        attr.mp_size = data_layout.size() as u32;
        unsafe {
            let mp_id = osMemoryPoolNew(block_count as u32, block_size as u32, &attr as *const _);
            assert_eq!(osMemoryPoolGetBlockSize(mp_id), block_size as u32);
            assert_eq!(osMemoryPoolGetCapacity(mp_id), block_count as u32);
            assert_eq!(osMemoryPoolGetCount(mp_id), 0);
            assert_eq!(osMemoryPoolGetSpace(mp_id), block_count as u32);
            let block = osMemoryPoolAlloc(mp_id, 1024);
            assert!(!block.is_null());
            assert_eq!(osMemoryPoolDelete(mp_id), osStatus_t_osErrorResource);
            assert_eq!(osMemoryPoolFree(mp_id, block), osStatus_t_osOK);
        }
    }

    #[test]
    fn test_c_mempool_new_rejects_size_overflow() {
        // Regression test: `block_count * block_size` must not wrap around.
        // 2 * 0x8000_0000 wraps to 0 in u32 and used to pass the `mp_size`
        // check with a tiny buffer, handing out block pointers past its end.
        unsafe {
            assert!(osMemoryPoolNew(2, 0x8000_0000, core::ptr::null()).is_null());
            assert!(osMemoryPoolNew(0x1_0000, 0x1_0000, core::ptr::null()).is_null());
            // Zero sized pools are rejected as well.
            assert!(osMemoryPoolNew(0, 512, core::ptr::null()).is_null());
            assert!(osMemoryPoolNew(4, 0, core::ptr::null()).is_null());
        }
    }

    #[test]
    fn test_c_mempool_new_with_given_mp_mem_size_check() {
        let mut attr: osMemoryPoolAttr_t = unsafe { core::mem::zeroed() };
        let mut mp_mem = [0u8; 64];
        attr.mp_mem = mp_mem.as_mut_ptr() as *mut c_void;
        attr.mp_size = 64;
        unsafe {
            // The wrapped product must not pass the `mp_size` check.
            assert!(osMemoryPoolNew(2, 0x8000_0000, &attr as *const _).is_null());
            // A pool that fits into the provided memory is still accepted.
            let mp_id = osMemoryPoolNew(2, 32, &attr as *const _);
            assert!(!mp_id.is_null());
            assert_eq!(osMemoryPoolGetCapacity(mp_id), 2);
            assert_eq!(osMemoryPoolGetBlockSize(mp_id), 32);
            let block = osMemoryPoolAlloc(mp_id, 1024);
            assert!(!block.is_null());
            assert_eq!(osMemoryPoolFree(mp_id, block), osStatus_t_osOK);
            assert_eq!(osMemoryPoolDelete(mp_id), osStatus_t_osOK);
        }
    }
}
