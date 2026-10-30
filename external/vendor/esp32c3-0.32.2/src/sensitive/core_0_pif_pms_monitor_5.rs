#[doc = "Register `CORE_0_PIF_PMS_MONITOR_5` reader"]
pub type R = crate::R<CORE_0_PIF_PMS_MONITOR_5_SPEC>;
#[doc = "Field `CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_INTR` reader - core_0_pif_pms_monitor_nonword_violate_intr"]
pub type CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_INTR_R = crate::BitReader;
#[doc = "Field `CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_STATUS_HSIZE` reader - core_0_pif_pms_monitor_nonword_violate_status_hsize"]
pub type CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_STATUS_HSIZE_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_STATUS_HWORLD` reader - core_0_pif_pms_monitor_nonword_violate_status_hworld"]
pub type CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_STATUS_HWORLD_R = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - core_0_pif_pms_monitor_nonword_violate_intr"]
    #[inline(always)]
    pub fn core_0_pif_pms_monitor_nonword_violate_intr(
        &self,
    ) -> CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_INTR_R {
        CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_INTR_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:2 - core_0_pif_pms_monitor_nonword_violate_status_hsize"]
    #[inline(always)]
    pub fn core_0_pif_pms_monitor_nonword_violate_status_hsize(
        &self,
    ) -> CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_STATUS_HSIZE_R {
        CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_STATUS_HSIZE_R::new(((self.bits >> 1) & 3) as u8)
    }
    #[doc = "Bits 3:4 - core_0_pif_pms_monitor_nonword_violate_status_hworld"]
    #[inline(always)]
    pub fn core_0_pif_pms_monitor_nonword_violate_status_hworld(
        &self,
    ) -> CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_STATUS_HWORLD_R {
        CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_STATUS_HWORLD_R::new(((self.bits >> 3) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE_0_PIF_PMS_MONITOR_5")
            .field(
                "core_0_pif_pms_monitor_nonword_violate_intr",
                &self.core_0_pif_pms_monitor_nonword_violate_intr(),
            )
            .field(
                "core_0_pif_pms_monitor_nonword_violate_status_hsize",
                &self.core_0_pif_pms_monitor_nonword_violate_status_hsize(),
            )
            .field(
                "core_0_pif_pms_monitor_nonword_violate_status_hworld",
                &self.core_0_pif_pms_monitor_nonword_violate_status_hworld(),
            )
            .finish()
    }
}
#[doc = "SENSITIVE_CORE_0_PIF_PMS_MONITOR_5_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_monitor_5::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE_0_PIF_PMS_MONITOR_5_SPEC;
impl crate::RegisterSpec for CORE_0_PIF_PMS_MONITOR_5_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core_0_pif_pms_monitor_5::R`](R) reader structure"]
impl crate::Readable for CORE_0_PIF_PMS_MONITOR_5_SPEC {}
#[doc = "`reset()` method sets CORE_0_PIF_PMS_MONITOR_5 to value 0"]
impl crate::Resettable for CORE_0_PIF_PMS_MONITOR_5_SPEC {}
