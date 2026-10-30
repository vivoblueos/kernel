#[doc = "Register `REGION_PMS_CONSTRAIN_0` reader"]
pub type R = crate::R<REGION_PMS_CONSTRAIN_0_SPEC>;
#[doc = "Register `REGION_PMS_CONSTRAIN_0` writer"]
pub type W = crate::W<REGION_PMS_CONSTRAIN_0_SPEC>;
#[doc = "Field `REGION_PMS_CONSTRAIN_LOCK` reader - region_pms_constrain_lock"]
pub type REGION_PMS_CONSTRAIN_LOCK_R = crate::BitReader;
#[doc = "Field `REGION_PMS_CONSTRAIN_LOCK` writer - region_pms_constrain_lock"]
pub type REGION_PMS_CONSTRAIN_LOCK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - region_pms_constrain_lock"]
    #[inline(always)]
    pub fn region_pms_constrain_lock(&self) -> REGION_PMS_CONSTRAIN_LOCK_R {
        REGION_PMS_CONSTRAIN_LOCK_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("REGION_PMS_CONSTRAIN_0")
            .field(
                "region_pms_constrain_lock",
                &self.region_pms_constrain_lock(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - region_pms_constrain_lock"]
    #[inline(always)]
    pub fn region_pms_constrain_lock(
        &mut self,
    ) -> REGION_PMS_CONSTRAIN_LOCK_W<'_, REGION_PMS_CONSTRAIN_0_SPEC> {
        REGION_PMS_CONSTRAIN_LOCK_W::new(self, 0)
    }
}
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REGION_PMS_CONSTRAIN_0_SPEC;
impl crate::RegisterSpec for REGION_PMS_CONSTRAIN_0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`region_pms_constrain_0::R`](R) reader structure"]
impl crate::Readable for REGION_PMS_CONSTRAIN_0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`region_pms_constrain_0::W`](W) writer structure"]
impl crate::Writable for REGION_PMS_CONSTRAIN_0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets REGION_PMS_CONSTRAIN_0 to value 0"]
impl crate::Resettable for REGION_PMS_CONSTRAIN_0_SPEC {}
