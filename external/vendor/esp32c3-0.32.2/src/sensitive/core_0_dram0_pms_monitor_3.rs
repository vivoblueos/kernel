#[doc = "Register `CORE_0_DRAM0_PMS_MONITOR_3` reader"]
pub type R = crate::R<CORE_0_DRAM0_PMS_MONITOR_3_SPEC>;
#[doc = "Field `CORE_0_DRAM0_PMS_MONITOR_VIOLATE_STATUS_WR` reader - core_0_dram0_pms_monitor_violate_status_wr"]
pub type CORE_0_DRAM0_PMS_MONITOR_VIOLATE_STATUS_WR_R = crate::BitReader;
#[doc = "Field `CORE_0_DRAM0_PMS_MONITOR_VIOLATE_STATUS_BYTEEN` reader - core_0_dram0_pms_monitor_violate_status_byteen"]
pub type CORE_0_DRAM0_PMS_MONITOR_VIOLATE_STATUS_BYTEEN_R = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - core_0_dram0_pms_monitor_violate_status_wr"]
    #[inline(always)]
    pub fn core_0_dram0_pms_monitor_violate_status_wr(
        &self,
    ) -> CORE_0_DRAM0_PMS_MONITOR_VIOLATE_STATUS_WR_R {
        CORE_0_DRAM0_PMS_MONITOR_VIOLATE_STATUS_WR_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:4 - core_0_dram0_pms_monitor_violate_status_byteen"]
    #[inline(always)]
    pub fn core_0_dram0_pms_monitor_violate_status_byteen(
        &self,
    ) -> CORE_0_DRAM0_PMS_MONITOR_VIOLATE_STATUS_BYTEEN_R {
        CORE_0_DRAM0_PMS_MONITOR_VIOLATE_STATUS_BYTEEN_R::new(((self.bits >> 1) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE_0_DRAM0_PMS_MONITOR_3")
            .field(
                "core_0_dram0_pms_monitor_violate_status_wr",
                &self.core_0_dram0_pms_monitor_violate_status_wr(),
            )
            .field(
                "core_0_dram0_pms_monitor_violate_status_byteen",
                &self.core_0_dram0_pms_monitor_violate_status_byteen(),
            )
            .finish()
    }
}
#[doc = "SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_dram0_pms_monitor_3::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE_0_DRAM0_PMS_MONITOR_3_SPEC;
impl crate::RegisterSpec for CORE_0_DRAM0_PMS_MONITOR_3_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core_0_dram0_pms_monitor_3::R`](R) reader structure"]
impl crate::Readable for CORE_0_DRAM0_PMS_MONITOR_3_SPEC {}
#[doc = "`reset()` method sets CORE_0_DRAM0_PMS_MONITOR_3 to value 0"]
impl crate::Resettable for CORE_0_DRAM0_PMS_MONITOR_3_SPEC {}
