//! Hypercalls for x86-64 pKVM.

use core::arch::asm;
use zerocopy::{FromBytes, Immutable, IntoBytes};

/// This CPUID returns the signature and should be used to determine if VM is running under pKVM,
/// KVM or not. See the Linux header `arch/x86/include/uapi/asm/kvm_para.h`.
const KVM_CPUID_SIGNATURE: u32 = 0x40000000;

// See `include/uapi/linux/kvm_para.h`. (These hypercalls numbers can change depending on the
// upstream progress.)
const KVM_HC_PKVM_OP: u32 = 20;
const PKVM_GHC_IOREAD: u32 = KVM_HC_PKVM_OP + 3;
const PKVM_GHC_IOWRITE: u32 = KVM_HC_PKVM_OP + 4;

/// The maximum number of bytes that can be read or written by a single IO hypercall.
const HYP_IO_MAX: usize = 8;

/// Gets the signature CPU ID.
pub fn cpuid_signature() -> [u8; 4] {
    let signature: u32;

    // SAFETY: Assembly call. The argument for cpuid is passed via rax and in case of
    // KVM_CPUID_SIGNATURE returned via rbx, rcx and rdx. Ideally using a named argument in
    // inline asm for rbx would be more straightforward, but when "rbx" is directly used
    // LLVM complains that it is used internally.
    //
    // Therefore use r8 instead and push rbx to the stack before making cpuid call, store
    // rbx content to r8 as use it as inline asm output and pop the rbx.
    unsafe {
        asm!(
            "push rbx",
            "cpuid",
            "mov r8, rbx",
            "pop rbx",
            in("eax") KVM_CPUID_SIGNATURE,
            out("r8") signature,
            out("rcx") _,
            out("rdx") _,
        );
    };
    signature.to_le_bytes()
}

/// Asks the hypervisor to perform an IO read at the given physical address.
pub fn hyp_io_read(address: usize, size: usize) -> u64 {
    let data;

    // SAFETY: Assembly call. Arguments for vmcall are passed via rax, rbx, rcx and rdx. Ideally
    // using a named argument in the inline asm for rbx would be more straightforward, but when
    // "rbx" is used directly LLVM complains that it is used internally.
    //
    // Therefore use r8 temporary, push rbx to the stack, perform proper call and pop rbx again.
    unsafe {
        asm!(
            "push rbx",
            "mov rbx, r8",
            "vmcall",
            "pop rbx",
            inout("rax") u64::from(PKVM_GHC_IOREAD) => data,
            in("r8") address,
            in("rcx") size,
        );
    }
    data
}

/// Asks the hypervisor to perform an IO write at the given physical address.
pub fn hyp_io_write(address: usize, size: usize, data: u64) {
    // SAFETY: Assembly call. Arguments for vmcall are passed via rax, rbx, rcx and rdx. Ideally
    // using a named argument in the inline asm for rbx would be more straightforward but when
    // "rbx" is used directly used LLVM complains that it is used internally.
    //
    // Therefore use r8 temporary, push rbx to the stack, perform proper call and pop rbx again.
    unsafe {
        asm!(
            "push rbx",
            "mov rbx, r8",
            "vmcall",
            "pop rbx",
            in("rax") PKVM_GHC_IOWRITE,
            in("r8") address,
            in("rcx") size,
            in("rdx") data,
        );
    }
}

/// A region of physical address space which may be accessed by IO read and/or write hypercalls.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HypIoRegion {
    /// The physical address of the start of the IO region.
    pub paddr: usize,
    /// The size of the IO region in bytes.
    pub size: usize,
}

impl HypIoRegion {
    pub fn read<T: FromBytes>(self, offset: usize) -> T {
        assert!(offset + size_of::<T>() <= self.size);
        assert!(size_of::<T>() <= HYP_IO_MAX);

        let data = hyp_io_read(self.paddr + offset, size_of::<T>());
        T::read_from_prefix(data.as_bytes()).unwrap().0
    }

    pub fn write<T: IntoBytes + Immutable>(self, offset: usize, value: T) {
        assert!(offset + size_of::<T>() <= self.size);
        assert!(size_of::<T>() <= HYP_IO_MAX);

        let mut data = 0;
        data.as_mut_bytes()[..size_of::<T>()].copy_from_slice(value.as_bytes());
        hyp_io_write(self.paddr + offset, size_of::<T>(), data);
    }
}
