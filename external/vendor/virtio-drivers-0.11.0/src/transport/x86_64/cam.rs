use super::hypercalls::{cpuid_signature, hyp_io_read, hyp_io_write};
use crate::transport::pci::bus::{Cam, ConfigurationAccess, DeviceFunction};

const PKVM_SIGNATURE: &[u8] = b"PKVM";

/// A PCI configuration access mechanism using hypercalls implemented by the x86-64 pKVM hypervisor.
pub struct HypCam {
    /// The physical base address of the PCI root complex.
    phys_base: usize,
    cam: Cam,
}

impl HypCam {
    /// Creates a new `HypCam` for the PCI root complex at the given physical base address.
    pub fn new(phys_base: usize, cam: Cam) -> Self {
        Self { phys_base, cam }
    }

    /// Returns whether we are running under pKVM by checking the CPU ID signature.
    pub fn is_pkvm() -> bool {
        cpuid_signature() == PKVM_SIGNATURE
    }
}

impl ConfigurationAccess for HypCam {
    fn read_word(&self, device_function: DeviceFunction, register_offset: u8) -> u32 {
        let address = self.cam.cam_offset(device_function, register_offset);
        hyp_io_read(self.phys_base + (address as usize), 4) as u32
    }

    fn write_word(&mut self, device_function: DeviceFunction, register_offset: u8, data: u32) {
        let address = self.cam.cam_offset(device_function, register_offset);
        hyp_io_write(self.phys_base + (address as usize), 4, data.into());
    }

    unsafe fn unsafe_clone(&self) -> Self {
        Self {
            phys_base: self.phys_base,
            cam: self.cam,
        }
    }
}
