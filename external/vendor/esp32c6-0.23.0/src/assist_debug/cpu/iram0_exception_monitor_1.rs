#[doc = "Register `IRAM0_EXCEPTION_MONITOR_1` reader"]
pub type R = crate::R<IRAM0_EXCEPTION_MONITOR_1_SPEC>;
#[doc = "Field `IRAM0_RECORDING_ADDR_1` reader - reg_core_0_iram0_recording_addr_1"]
pub type IRAM0_RECORDING_ADDR_1_R = crate::FieldReader<u32>;
#[doc = "Field `IRAM0_RECORDING_WR_1` reader - reg_core_0_iram0_recording_wr_1"]
pub type IRAM0_RECORDING_WR_1_R = crate::BitReader;
#[doc = "Field `IRAM0_RECORDING_LOADSTORE_1` reader - reg_core_0_iram0_recording_loadstore_1"]
pub type IRAM0_RECORDING_LOADSTORE_1_R = crate::BitReader;
impl R {
    #[doc = "Bits 0:23 - reg_core_0_iram0_recording_addr_1"]
    #[inline(always)]
    pub fn iram0_recording_addr_1(&self) -> IRAM0_RECORDING_ADDR_1_R {
        IRAM0_RECORDING_ADDR_1_R::new(self.bits & 0x00ff_ffff)
    }
    #[doc = "Bit 24 - reg_core_0_iram0_recording_wr_1"]
    #[inline(always)]
    pub fn iram0_recording_wr_1(&self) -> IRAM0_RECORDING_WR_1_R {
        IRAM0_RECORDING_WR_1_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - reg_core_0_iram0_recording_loadstore_1"]
    #[inline(always)]
    pub fn iram0_recording_loadstore_1(&self) -> IRAM0_RECORDING_LOADSTORE_1_R {
        IRAM0_RECORDING_LOADSTORE_1_R::new(((self.bits >> 25) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IRAM0_EXCEPTION_MONITOR_1")
            .field("iram0_recording_addr_1", &self.iram0_recording_addr_1())
            .field("iram0_recording_wr_1", &self.iram0_recording_wr_1())
            .field(
                "iram0_recording_loadstore_1",
                &self.iram0_recording_loadstore_1(),
            )
            .finish()
    }
}
#[doc = "exception monitor status register1\n\nYou can [`read`](crate::Reg::read) this register and get [`iram0_exception_monitor_1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IRAM0_EXCEPTION_MONITOR_1_SPEC;
impl crate::RegisterSpec for IRAM0_EXCEPTION_MONITOR_1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`iram0_exception_monitor_1::R`](R) reader structure"]
impl crate::Readable for IRAM0_EXCEPTION_MONITOR_1_SPEC {}
#[doc = "`reset()` method sets IRAM0_EXCEPTION_MONITOR_1 to value 0"]
impl crate::Resettable for IRAM0_EXCEPTION_MONITOR_1_SPEC {}
