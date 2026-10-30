#[doc = "Register `SAR_CCT` reader"]
pub type R = crate::R<SAR_CCT_SPEC>;
#[doc = "Register `SAR_CCT` writer"]
pub type W = crate::W<SAR_CCT_SPEC>;
#[doc = "Field `SAR2_PWDET_CCT` reader - need_des"]
pub type SAR2_PWDET_CCT_R = crate::FieldReader;
#[doc = "Field `SAR2_PWDET_CCT` writer - need_des"]
pub type SAR2_PWDET_CCT_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
impl R {
    #[doc = "Bits 29:31 - need_des"]
    #[inline(always)]
    pub fn sar2_pwdet_cct(&self) -> SAR2_PWDET_CCT_R {
        SAR2_PWDET_CCT_R::new(((self.bits >> 29) & 7) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SAR_CCT")
            .field("sar2_pwdet_cct", &self.sar2_pwdet_cct())
            .finish()
    }
}
impl W {
    #[doc = "Bits 29:31 - need_des"]
    #[inline(always)]
    pub fn sar2_pwdet_cct(&mut self) -> SAR2_PWDET_CCT_W<'_, SAR_CCT_SPEC> {
        SAR2_PWDET_CCT_W::new(self, 29)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`sar_cct::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sar_cct::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SAR_CCT_SPEC;
impl crate::RegisterSpec for SAR_CCT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sar_cct::R`](R) reader structure"]
impl crate::Readable for SAR_CCT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sar_cct::W`](W) writer structure"]
impl crate::Writable for SAR_CCT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SAR_CCT to value 0"]
impl crate::Resettable for SAR_CCT_SPEC {}
