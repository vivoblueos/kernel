#[doc = "Register `BACKUP_BUS_PMS_MONITOR_2` reader"]
pub type R = crate::R<BACKUP_BUS_PMS_MONITOR_2_SPEC>;
#[doc = "Field `BACKUP_BUS_PMS_MONITOR_VIOLATE_INTR` reader - backup_bus_pms_monitor_violate_intr"]
pub type BACKUP_BUS_PMS_MONITOR_VIOLATE_INTR_R = crate::BitReader;
#[doc = "Field `BACKUP_BUS_PMS_MONITOR_VIOLATE_STATUS_HTRANS` reader - backup_bus_pms_monitor_violate_status_htrans"]
pub type BACKUP_BUS_PMS_MONITOR_VIOLATE_STATUS_HTRANS_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_MONITOR_VIOLATE_STATUS_HSIZE` reader - backup_bus_pms_monitor_violate_status_hsize"]
pub type BACKUP_BUS_PMS_MONITOR_VIOLATE_STATUS_HSIZE_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_MONITOR_VIOLATE_STATUS_HWRITE` reader - backup_bus_pms_monitor_violate_status_hwrite"]
pub type BACKUP_BUS_PMS_MONITOR_VIOLATE_STATUS_HWRITE_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - backup_bus_pms_monitor_violate_intr"]
    #[inline(always)]
    pub fn backup_bus_pms_monitor_violate_intr(&self) -> BACKUP_BUS_PMS_MONITOR_VIOLATE_INTR_R {
        BACKUP_BUS_PMS_MONITOR_VIOLATE_INTR_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:2 - backup_bus_pms_monitor_violate_status_htrans"]
    #[inline(always)]
    pub fn backup_bus_pms_monitor_violate_status_htrans(
        &self,
    ) -> BACKUP_BUS_PMS_MONITOR_VIOLATE_STATUS_HTRANS_R {
        BACKUP_BUS_PMS_MONITOR_VIOLATE_STATUS_HTRANS_R::new(((self.bits >> 1) & 3) as u8)
    }
    #[doc = "Bits 3:5 - backup_bus_pms_monitor_violate_status_hsize"]
    #[inline(always)]
    pub fn backup_bus_pms_monitor_violate_status_hsize(
        &self,
    ) -> BACKUP_BUS_PMS_MONITOR_VIOLATE_STATUS_HSIZE_R {
        BACKUP_BUS_PMS_MONITOR_VIOLATE_STATUS_HSIZE_R::new(((self.bits >> 3) & 7) as u8)
    }
    #[doc = "Bit 6 - backup_bus_pms_monitor_violate_status_hwrite"]
    #[inline(always)]
    pub fn backup_bus_pms_monitor_violate_status_hwrite(
        &self,
    ) -> BACKUP_BUS_PMS_MONITOR_VIOLATE_STATUS_HWRITE_R {
        BACKUP_BUS_PMS_MONITOR_VIOLATE_STATUS_HWRITE_R::new(((self.bits >> 6) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BACKUP_BUS_PMS_MONITOR_2")
            .field(
                "backup_bus_pms_monitor_violate_intr",
                &self.backup_bus_pms_monitor_violate_intr(),
            )
            .field(
                "backup_bus_pms_monitor_violate_status_htrans",
                &self.backup_bus_pms_monitor_violate_status_htrans(),
            )
            .field(
                "backup_bus_pms_monitor_violate_status_hsize",
                &self.backup_bus_pms_monitor_violate_status_hsize(),
            )
            .field(
                "backup_bus_pms_monitor_violate_status_hwrite",
                &self.backup_bus_pms_monitor_violate_status_hwrite(),
            )
            .finish()
    }
}
#[doc = "SENSITIVE_BACKUP_BUS_PMS_MONITOR_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_monitor_2::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BACKUP_BUS_PMS_MONITOR_2_SPEC;
impl crate::RegisterSpec for BACKUP_BUS_PMS_MONITOR_2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`backup_bus_pms_monitor_2::R`](R) reader structure"]
impl crate::Readable for BACKUP_BUS_PMS_MONITOR_2_SPEC {}
#[doc = "`reset()` method sets BACKUP_BUS_PMS_MONITOR_2 to value 0"]
impl crate::Resettable for BACKUP_BUS_PMS_MONITOR_2_SPEC {}
