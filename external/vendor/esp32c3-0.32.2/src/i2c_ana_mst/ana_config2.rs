#[doc = "Register `ANA_CONFIG2` reader"]
pub type R = crate::R<ANA_CONFIG2_SPEC>;
#[doc = "Register `ANA_CONFIG2` writer"]
pub type W = crate::W<ANA_CONFIG2_SPEC>;
#[doc = "Field `SAR_FORCE_PU` reader - ?"]
pub type SAR_FORCE_PU_R = crate::BitReader;
#[doc = "Field `SAR_FORCE_PU` writer - ?"]
pub type SAR_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAR_FORCE_PD` reader - ?"]
pub type SAR_FORCE_PD_R = crate::BitReader;
#[doc = "Field `SAR_FORCE_PD` writer - ?"]
pub type SAR_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 16 - ?"]
    #[inline(always)]
    pub fn sar_force_pu(&self) -> SAR_FORCE_PU_R {
        SAR_FORCE_PU_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 18 - ?"]
    #[inline(always)]
    pub fn sar_force_pd(&self) -> SAR_FORCE_PD_R {
        SAR_FORCE_PD_R::new(((self.bits >> 18) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ANA_CONFIG2")
            .field("sar_force_pd", &self.sar_force_pd())
            .field("sar_force_pu", &self.sar_force_pu())
            .finish()
    }
}
impl W {
    #[doc = "Bit 16 - ?"]
    #[inline(always)]
    pub fn sar_force_pu(&mut self) -> SAR_FORCE_PU_W<'_, ANA_CONFIG2_SPEC> {
        SAR_FORCE_PU_W::new(self, 16)
    }
    #[doc = "Bit 18 - ?"]
    #[inline(always)]
    pub fn sar_force_pd(&mut self) -> SAR_FORCE_PD_W<'_, ANA_CONFIG2_SPEC> {
        SAR_FORCE_PD_W::new(self, 18)
    }
}
#[doc = "ANA_CONFIG2 register\n\nYou can [`read`](crate::Reg::read) this register and get [`ana_config2::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ana_config2::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ANA_CONFIG2_SPEC;
impl crate::RegisterSpec for ANA_CONFIG2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ana_config2::R`](R) reader structure"]
impl crate::Readable for ANA_CONFIG2_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ana_config2::W`](W) writer structure"]
impl crate::Writable for ANA_CONFIG2_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ANA_CONFIG2 to value 0"]
impl crate::Resettable for ANA_CONFIG2_SPEC {}
