#[doc = "Register `DRAM0_EXCEPTION_MONITOR_2` reader"]
pub type R = crate::R<DRAM0_EXCEPTION_MONITOR_2_SPEC>;
#[doc = "Field `DRAM0_RECORDING_ADDR_1` reader - reg_core_0_dram0_recording_addr_1"]
pub type DRAM0_RECORDING_ADDR_1_R = crate::FieldReader<u32>;
#[doc = "Field `DRAM0_RECORDING_WR_1` reader - reg_core_0_dram0_recording_wr_1"]
pub type DRAM0_RECORDING_WR_1_R = crate::BitReader;
#[doc = "Field `DRAM0_RECORDING_BYTEEN_1` reader - reg_core_0_dram0_recording_byteen_1"]
pub type DRAM0_RECORDING_BYTEEN_1_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:23 - reg_core_0_dram0_recording_addr_1"]
    #[inline(always)]
    pub fn dram0_recording_addr_1(&self) -> DRAM0_RECORDING_ADDR_1_R {
        DRAM0_RECORDING_ADDR_1_R::new(self.bits & 0x00ff_ffff)
    }
    #[doc = "Bit 24 - reg_core_0_dram0_recording_wr_1"]
    #[inline(always)]
    pub fn dram0_recording_wr_1(&self) -> DRAM0_RECORDING_WR_1_R {
        DRAM0_RECORDING_WR_1_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bits 25:28 - reg_core_0_dram0_recording_byteen_1"]
    #[inline(always)]
    pub fn dram0_recording_byteen_1(&self) -> DRAM0_RECORDING_BYTEEN_1_R {
        DRAM0_RECORDING_BYTEEN_1_R::new(((self.bits >> 25) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DRAM0_EXCEPTION_MONITOR_2")
            .field("dram0_recording_addr_1", &self.dram0_recording_addr_1())
            .field("dram0_recording_wr_1", &self.dram0_recording_wr_1())
            .field("dram0_recording_byteen_1", &self.dram0_recording_byteen_1())
            .finish()
    }
}
#[doc = "exception monitor status register4\n\nYou can [`read`](crate::Reg::read) this register and get [`dram0_exception_monitor_2::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DRAM0_EXCEPTION_MONITOR_2_SPEC;
impl crate::RegisterSpec for DRAM0_EXCEPTION_MONITOR_2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dram0_exception_monitor_2::R`](R) reader structure"]
impl crate::Readable for DRAM0_EXCEPTION_MONITOR_2_SPEC {}
#[doc = "`reset()` method sets DRAM0_EXCEPTION_MONITOR_2 to value 0"]
impl crate::Resettable for DRAM0_EXCEPTION_MONITOR_2_SPEC {}
