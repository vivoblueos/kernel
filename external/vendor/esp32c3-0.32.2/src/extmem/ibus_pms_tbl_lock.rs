#[doc = "Register `IBUS_PMS_TBL_LOCK` reader"]
pub type R = crate::R<IBUS_PMS_TBL_LOCK_SPEC>;
#[doc = "Register `IBUS_PMS_TBL_LOCK` writer"]
pub type W = crate::W<IBUS_PMS_TBL_LOCK_SPEC>;
#[doc = "Field `IBUS_PMS_LOCK` reader - The bit is used to configure the ibus permission control section boundary0"]
pub type IBUS_PMS_LOCK_R = crate::BitReader;
#[doc = "Field `IBUS_PMS_LOCK` writer - The bit is used to configure the ibus permission control section boundary0"]
pub type IBUS_PMS_LOCK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The bit is used to configure the ibus permission control section boundary0"]
    #[inline(always)]
    pub fn ibus_pms_lock(&self) -> IBUS_PMS_LOCK_R {
        IBUS_PMS_LOCK_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IBUS_PMS_TBL_LOCK")
            .field("ibus_pms_lock", &self.ibus_pms_lock())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to configure the ibus permission control section boundary0"]
    #[inline(always)]
    pub fn ibus_pms_lock(&mut self) -> IBUS_PMS_LOCK_W<'_, IBUS_PMS_TBL_LOCK_SPEC> {
        IBUS_PMS_LOCK_W::new(self, 0)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`ibus_pms_tbl_lock::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ibus_pms_tbl_lock::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IBUS_PMS_TBL_LOCK_SPEC;
impl crate::RegisterSpec for IBUS_PMS_TBL_LOCK_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ibus_pms_tbl_lock::R`](R) reader structure"]
impl crate::Readable for IBUS_PMS_TBL_LOCK_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ibus_pms_tbl_lock::W`](W) writer structure"]
impl crate::Writable for IBUS_PMS_TBL_LOCK_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IBUS_PMS_TBL_LOCK to value 0"]
impl crate::Resettable for IBUS_PMS_TBL_LOCK_SPEC {}
