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

use blueos_infra::storage::Storage;
use core::alloc::Layout;

pub type Result<T> = core::result::Result<T, &'static str>;

#[derive(Debug)]
pub struct MemoryMapper {
    virtual_entry: usize,
    virtual_start: usize,
    virtual_end: usize,
    mem: Storage,
}

impl MemoryMapper {
    #[inline]
    pub fn new() -> Self {
        Self {
            virtual_entry: 0,
            virtual_start: usize::MAX,
            virtual_end: 0,
            mem: Storage::default(),
        }
    }

    #[inline]
    pub fn entry(&self) -> usize {
        self.virtual_entry
    }

    #[inline]
    pub fn set_entry(&mut self, entry: usize) -> &mut Self {
        self.virtual_entry = entry;
        self
    }

    #[inline]
    pub fn start(&self) -> usize {
        self.virtual_start
    }

    #[inline]
    pub fn update_start(&mut self, val: usize) -> &mut Self {
        self.virtual_start = core::cmp::min(self.virtual_start, val);
        self
    }

    #[inline]
    pub fn update_end(&mut self, val: usize) -> &mut Self {
        self.virtual_end = core::cmp::max(self.virtual_end, val);
        self
    }

    #[inline]
    pub fn total_size(&self) -> Result<usize> {
        if self.virtual_end < self.virtual_start {
            return Err("Illegal memory size");
        }
        Ok(self.virtual_end - self.virtual_start)
    }

    #[inline]
    pub fn allocate_memory(&mut self) -> Result<usize> {
        // FIXME: We are not using paging yet, so alignment(usually
        // 4096) specified in program header is not applied here.
        #[cfg(any(target_arch = "aarch64", target_arch = "riscv64"))]
        const ALIGN: usize = 4096;
        #[cfg(not(any(target_arch = "aarch64", target_arch = "riscv64")))]
        const ALIGN: usize = 2 * core::mem::size_of::<usize>();
        let Ok(layout) = Layout::from_size_align(self.total_size()?, ALIGN) else {
            return Err("Illegal memory layout");
        };
        self.mem = Storage::from_layout(layout);
        Ok(self.mem.size())
    }

    #[inline]
    pub fn real_start(&self) -> Result<usize> {
        let base = self.mem.base();
        if base.is_null() {
            return Err("Memory not allocated yet");
        }
        Ok(base as usize)
    }

    #[inline]
    pub fn real_entry(&self) -> Result<usize> {
        Ok(self.inner_real_ptr(self.virtual_entry)? as usize)
    }

    fn inner_real_offset(&self, vaddr: usize) -> Result<usize> {
        if vaddr < self.virtual_start || vaddr >= self.virtual_end {
            return Err("The address is in an illegal memory region");
        }
        let total_size = self.total_size()?;
        let offset = vaddr - self.virtual_start;
        if offset >= total_size {
            return Err("The address is in an illegal memory region");
        }
        Ok(offset)
    }

    fn inner_real_ptr(&self, vaddr: usize) -> Result<*mut u8> {
        let offset = self.inner_real_offset(vaddr)?;
        if offset >= self.mem.size() {
            return Err("The offset is beyond the allocated memory region");
        }
        let base = self.mem.base();
        if base.is_null() {
            return Err("Memory not allocated yet");
        }
        Ok(unsafe { base.add(offset) })
    }

    pub fn write_slice_at(&mut self, vaddr: usize, data: &[u8]) -> Result<usize> {
        if vaddr < self.virtual_start || vaddr + data.len() > self.virtual_end {
            return Err("The address is in an illegal memory region");
        }
        let real_begin = self.inner_real_ptr(vaddr)?;
        let _real_end = core::hint::black_box(self.inner_real_ptr(vaddr + data.len())?);
        // FIXME: Is it safe enough to use copy_nonoverlapping?
        unsafe { core::ptr::copy(data.as_ptr(), real_begin, data.len()) };
        Ok(data.len())
    }

    pub fn write_value_at<T>(&mut self, vaddr: usize, val: T) -> Result<usize>
    where
        T: Sized,
    {
        let size = core::mem::size_of::<T>();
        if vaddr < self.virtual_start || vaddr + size > self.virtual_end {
            return Err("The address is in an illegal memory region");
        }
        let real_begin = self.inner_real_ptr(vaddr)?;
        let _real_end = core::hint::black_box(self.inner_real_ptr(vaddr + size)?);
        let val_ptr: *mut T = unsafe { core::mem::transmute(real_begin) };
        unsafe { val_ptr.write(val) };
        Ok(size)
    }
}
