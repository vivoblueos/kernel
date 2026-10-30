#[doc = "Register `BACKUP_BUS_PMS_MONITOR_3` reader"]
pub type R = crate::R<BACKUP_BUS_PMS_MONITOR_3_SPEC>;
#[doc = "Field `BACKUP_BUS_PMS_MONITOR_VIOLATE_HADDR` reader - backup_bus_pms_monitor_violate_haddr"]
pub type BACKUP_BUS_PMS_MONITOR_VIOLATE_HADDR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - backup_bus_pms_monitor_violate_haddr"]
    #[inline(always)]
    pub fn backup_bus_pms_monitor_violate_haddr(&self) -> BACKUP_BUS_PMS_MONITOR_VIOLATE_HADDR_R {
        BACKUP_BUS_PMS_MONITOR_VIOLATE_HADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BACKUP_BUS_PMS_MONITOR_3")
            .field(
                "backup_bus_pms_monitor_violate_haddr",
                &self.backup_bus_pms_monitor_violate_haddr(),
            )
            .finish()
    }
}
#[doc = "SENSITIVE_BACKUP_BUS_PMS_MONITOR_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_monitor_3::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BACKUP_BUS_PMS_MONITOR_3_SPEC;
impl crate::RegisterSpec for BACKUP_BUS_PMS_MONITOR_3_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`backup_bus_pms_monitor_3::R`](R) reader structure"]
impl crate::Readable for BACKUP_BUS_PMS_MONITOR_3_SPEC {}
#[doc = "`reset()` method sets BACKUP_BUS_PMS_MONITOR_3 to value 0"]
impl crate::Resettable for BACKUP_BUS_PMS_MONITOR_3_SPEC {}
