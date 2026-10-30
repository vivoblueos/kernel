#[doc = "Register `DRAM0_EXCEPTION_MONITOR_3` reader"]
pub type R = crate::R<DRAM0_EXCEPTION_MONITOR_3_SPEC>;
#[doc = "Field `DRAM0_RECORDING_PC_1` reader - reg_core_0_dram0_recording_pc_1"]
pub type DRAM0_RECORDING_PC_1_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - reg_core_0_dram0_recording_pc_1"]
    #[inline(always)]
    pub fn dram0_recording_pc_1(&self) -> DRAM0_RECORDING_PC_1_R {
        DRAM0_RECORDING_PC_1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DRAM0_EXCEPTION_MONITOR_3")
            .field("dram0_recording_pc_1", &self.dram0_recording_pc_1())
            .finish()
    }
}
#[doc = "ASSIST_DEBUG_CORE_0_DRAM0_EXCEPTION_MONITOR_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`dram0_exception_monitor_3::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DRAM0_EXCEPTION_MONITOR_3_SPEC;
impl crate::RegisterSpec for DRAM0_EXCEPTION_MONITOR_3_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dram0_exception_monitor_3::R`](R) reader structure"]
impl crate::Readable for DRAM0_EXCEPTION_MONITOR_3_SPEC {}
#[doc = "`reset()` method sets DRAM0_EXCEPTION_MONITOR_3 to value 0"]
impl crate::Resettable for DRAM0_EXCEPTION_MONITOR_3_SPEC {}
