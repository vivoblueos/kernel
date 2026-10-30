#[doc = "Register `IRAM0_EXCEPTION_MONITOR_0` reader"]
pub type R = crate::R<IRAM0_EXCEPTION_MONITOR_0_SPEC>;
#[doc = "Field `IRAM0_RECORDING_ADDR_0` reader - reg_core_0_iram0_recording_addr_0"]
pub type IRAM0_RECORDING_ADDR_0_R = crate::FieldReader<u32>;
#[doc = "Field `IRAM0_RECORDING_WR_0` reader - reg_core_0_iram0_recording_wr_0"]
pub type IRAM0_RECORDING_WR_0_R = crate::BitReader;
#[doc = "Field `IRAM0_RECORDING_LOADSTORE_0` reader - reg_core_0_iram0_recording_loadstore_0"]
pub type IRAM0_RECORDING_LOADSTORE_0_R = crate::BitReader;
impl R {
    #[doc = "Bits 0:23 - reg_core_0_iram0_recording_addr_0"]
    #[inline(always)]
    pub fn iram0_recording_addr_0(&self) -> IRAM0_RECORDING_ADDR_0_R {
        IRAM0_RECORDING_ADDR_0_R::new(self.bits & 0x00ff_ffff)
    }
    #[doc = "Bit 24 - reg_core_0_iram0_recording_wr_0"]
    #[inline(always)]
    pub fn iram0_recording_wr_0(&self) -> IRAM0_RECORDING_WR_0_R {
        IRAM0_RECORDING_WR_0_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - reg_core_0_iram0_recording_loadstore_0"]
    #[inline(always)]
    pub fn iram0_recording_loadstore_0(&self) -> IRAM0_RECORDING_LOADSTORE_0_R {
        IRAM0_RECORDING_LOADSTORE_0_R::new(((self.bits >> 25) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IRAM0_EXCEPTION_MONITOR_0")
            .field("iram0_recording_addr_0", &self.iram0_recording_addr_0())
            .field("iram0_recording_wr_0", &self.iram0_recording_wr_0())
            .field(
                "iram0_recording_loadstore_0",
                &self.iram0_recording_loadstore_0(),
            )
            .finish()
    }
}
#[doc = "ASSIST_DEBUG_CORE_0_RCD_PDEBUGSP_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`iram0_exception_monitor_0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IRAM0_EXCEPTION_MONITOR_0_SPEC;
impl crate::RegisterSpec for IRAM0_EXCEPTION_MONITOR_0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`iram0_exception_monitor_0::R`](R) reader structure"]
impl crate::Readable for IRAM0_EXCEPTION_MONITOR_0_SPEC {}
#[doc = "`reset()` method sets IRAM0_EXCEPTION_MONITOR_0 to value 0"]
impl crate::Resettable for IRAM0_EXCEPTION_MONITOR_0_SPEC {}
