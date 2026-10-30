#[doc = "Register `DBUS_PMS_TBL_LOCK` reader"]
pub type R = crate::R<DBUS_PMS_TBL_LOCK_SPEC>;
#[doc = "Register `DBUS_PMS_TBL_LOCK` writer"]
pub type W = crate::W<DBUS_PMS_TBL_LOCK_SPEC>;
#[doc = "Field `DBUS_PMS_LOCK` reader - The bit is used to configure the ibus permission control section boundary0"]
pub type DBUS_PMS_LOCK_R = crate::BitReader;
#[doc = "Field `DBUS_PMS_LOCK` writer - The bit is used to configure the ibus permission control section boundary0"]
pub type DBUS_PMS_LOCK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The bit is used to configure the ibus permission control section boundary0"]
    #[inline(always)]
    pub fn dbus_pms_lock(&self) -> DBUS_PMS_LOCK_R {
        DBUS_PMS_LOCK_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DBUS_PMS_TBL_LOCK")
            .field("dbus_pms_lock", &self.dbus_pms_lock())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to configure the ibus permission control section boundary0"]
    #[inline(always)]
    pub fn dbus_pms_lock(&mut self) -> DBUS_PMS_LOCK_W<'_, DBUS_PMS_TBL_LOCK_SPEC> {
        DBUS_PMS_LOCK_W::new(self, 0)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`dbus_pms_tbl_lock::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dbus_pms_tbl_lock::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DBUS_PMS_TBL_LOCK_SPEC;
impl crate::RegisterSpec for DBUS_PMS_TBL_LOCK_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dbus_pms_tbl_lock::R`](R) reader structure"]
impl crate::Readable for DBUS_PMS_TBL_LOCK_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dbus_pms_tbl_lock::W`](W) writer structure"]
impl crate::Writable for DBUS_PMS_TBL_LOCK_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DBUS_PMS_TBL_LOCK to value 0"]
impl crate::Resettable for DBUS_PMS_TBL_LOCK_SPEC {}
