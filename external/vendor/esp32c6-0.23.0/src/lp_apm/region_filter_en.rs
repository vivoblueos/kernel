#[doc = "Register `REGION_FILTER_EN` reader"]
pub type R = crate::R<REGION_FILTER_EN_SPEC>;
#[doc = "Register `REGION_FILTER_EN` writer"]
pub type W = crate::W<REGION_FILTER_EN_SPEC>;
#[doc = "Field `REGION_FILTER_EN` reader - Region filter enable"]
pub type REGION_FILTER_EN_R = crate::FieldReader;
#[doc = "Field `REGION_FILTER_EN` writer - Region filter enable"]
pub type REGION_FILTER_EN_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3 - Region filter enable"]
    #[inline(always)]
    pub fn region_filter_en(&self) -> REGION_FILTER_EN_R {
        REGION_FILTER_EN_R::new((self.bits & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("REGION_FILTER_EN")
            .field("region_filter_en", &self.region_filter_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3 - Region filter enable"]
    #[inline(always)]
    pub fn region_filter_en(&mut self) -> REGION_FILTER_EN_W<'_, REGION_FILTER_EN_SPEC> {
        REGION_FILTER_EN_W::new(self, 0)
    }
}
#[doc = "Region filter enable register\n\nYou can [`read`](crate::Reg::read) this register and get [`region_filter_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_filter_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REGION_FILTER_EN_SPEC;
impl crate::RegisterSpec for REGION_FILTER_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`region_filter_en::R`](R) reader structure"]
impl crate::Readable for REGION_FILTER_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`region_filter_en::W`](W) writer structure"]
impl crate::Writable for REGION_FILTER_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets REGION_FILTER_EN to value 0x01"]
impl crate::Resettable for REGION_FILTER_EN_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
