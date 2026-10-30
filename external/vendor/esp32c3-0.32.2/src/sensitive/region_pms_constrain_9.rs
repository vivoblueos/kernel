#[doc = "Register `REGION_PMS_CONSTRAIN_9` reader"]
pub type R = crate::R<REGION_PMS_CONSTRAIN_9_SPEC>;
#[doc = "Register `REGION_PMS_CONSTRAIN_9` writer"]
pub type W = crate::W<REGION_PMS_CONSTRAIN_9_SPEC>;
#[doc = "Field `REGION_PMS_CONSTRAIN_ADDR_6` reader - region_pms_constrain_addr_6"]
pub type REGION_PMS_CONSTRAIN_ADDR_6_R = crate::FieldReader<u32>;
#[doc = "Field `REGION_PMS_CONSTRAIN_ADDR_6` writer - region_pms_constrain_addr_6"]
pub type REGION_PMS_CONSTRAIN_ADDR_6_W<'a, REG> = crate::FieldWriter<'a, REG, 30, u32>;
impl R {
    #[doc = "Bits 0:29 - region_pms_constrain_addr_6"]
    #[inline(always)]
    pub fn region_pms_constrain_addr_6(&self) -> REGION_PMS_CONSTRAIN_ADDR_6_R {
        REGION_PMS_CONSTRAIN_ADDR_6_R::new(self.bits & 0x3fff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("REGION_PMS_CONSTRAIN_9")
            .field(
                "region_pms_constrain_addr_6",
                &self.region_pms_constrain_addr_6(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:29 - region_pms_constrain_addr_6"]
    #[inline(always)]
    pub fn region_pms_constrain_addr_6(
        &mut self,
    ) -> REGION_PMS_CONSTRAIN_ADDR_6_W<'_, REGION_PMS_CONSTRAIN_9_SPEC> {
        REGION_PMS_CONSTRAIN_ADDR_6_W::new(self, 0)
    }
}
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_9_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_9::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_9::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REGION_PMS_CONSTRAIN_9_SPEC;
impl crate::RegisterSpec for REGION_PMS_CONSTRAIN_9_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`region_pms_constrain_9::R`](R) reader structure"]
impl crate::Readable for REGION_PMS_CONSTRAIN_9_SPEC {}
#[doc = "`write(|w| ..)` method takes [`region_pms_constrain_9::W`](W) writer structure"]
impl crate::Writable for REGION_PMS_CONSTRAIN_9_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets REGION_PMS_CONSTRAIN_9 to value 0"]
impl crate::Resettable for REGION_PMS_CONSTRAIN_9_SPEC {}
