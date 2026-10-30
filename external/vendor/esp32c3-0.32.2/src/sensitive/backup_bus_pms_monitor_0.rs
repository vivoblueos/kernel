#[doc = "Register `BACKUP_BUS_PMS_MONITOR_0` reader"]
pub type R = crate::R<BACKUP_BUS_PMS_MONITOR_0_SPEC>;
#[doc = "Register `BACKUP_BUS_PMS_MONITOR_0` writer"]
pub type W = crate::W<BACKUP_BUS_PMS_MONITOR_0_SPEC>;
#[doc = "Field `BACKUP_BUS_PMS_MONITOR_LOCK` reader - backup_bus_pms_monitor_lock"]
pub type BACKUP_BUS_PMS_MONITOR_LOCK_R = crate::BitReader;
#[doc = "Field `BACKUP_BUS_PMS_MONITOR_LOCK` writer - backup_bus_pms_monitor_lock"]
pub type BACKUP_BUS_PMS_MONITOR_LOCK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - backup_bus_pms_monitor_lock"]
    #[inline(always)]
    pub fn backup_bus_pms_monitor_lock(&self) -> BACKUP_BUS_PMS_MONITOR_LOCK_R {
        BACKUP_BUS_PMS_MONITOR_LOCK_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BACKUP_BUS_PMS_MONITOR_0")
            .field(
                "backup_bus_pms_monitor_lock",
                &self.backup_bus_pms_monitor_lock(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - backup_bus_pms_monitor_lock"]
    #[inline(always)]
    pub fn backup_bus_pms_monitor_lock(
        &mut self,
    ) -> BACKUP_BUS_PMS_MONITOR_LOCK_W<'_, BACKUP_BUS_PMS_MONITOR_0_SPEC> {
        BACKUP_BUS_PMS_MONITOR_LOCK_W::new(self, 0)
    }
}
#[doc = "SENSITIVE_BACKUP_BUS_PMS_MONITOR_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_monitor_0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`backup_bus_pms_monitor_0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BACKUP_BUS_PMS_MONITOR_0_SPEC;
impl crate::RegisterSpec for BACKUP_BUS_PMS_MONITOR_0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`backup_bus_pms_monitor_0::R`](R) reader structure"]
impl crate::Readable for BACKUP_BUS_PMS_MONITOR_0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`backup_bus_pms_monitor_0::W`](W) writer structure"]
impl crate::Writable for BACKUP_BUS_PMS_MONITOR_0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets BACKUP_BUS_PMS_MONITOR_0 to value 0"]
impl crate::Resettable for BACKUP_BUS_PMS_MONITOR_0_SPEC {}
