#[doc = "Register `TSENS_SAMPLE` reader"]
pub type R = crate::R<TSENS_SAMPLE_SPEC>;
#[doc = "Register `TSENS_SAMPLE` writer"]
pub type W = crate::W<TSENS_SAMPLE_SPEC>;
#[doc = "Field `RATE` reader - HW sample rate"]
pub type RATE_R = crate::FieldReader<u16>;
#[doc = "Field `RATE` writer - HW sample rate"]
pub type RATE_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `EN` reader - HW sample en"]
pub type EN_R = crate::BitReader;
#[doc = "Field `EN` writer - HW sample en"]
pub type EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:15 - HW sample rate"]
    #[inline(always)]
    pub fn rate(&self) -> RATE_R {
        RATE_R::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bit 16 - HW sample en"]
    #[inline(always)]
    pub fn en(&self) -> EN_R {
        EN_R::new(((self.bits >> 16) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TSENS_SAMPLE")
            .field("rate", &self.rate())
            .field("en", &self.en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - HW sample rate"]
    #[inline(always)]
    pub fn rate(&mut self) -> RATE_W<'_, TSENS_SAMPLE_SPEC> {
        RATE_W::new(self, 0)
    }
    #[doc = "Bit 16 - HW sample en"]
    #[inline(always)]
    pub fn en(&mut self) -> EN_W<'_, TSENS_SAMPLE_SPEC> {
        EN_W::new(self, 16)
    }
}
#[doc = "digital tsens configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`tsens_sample::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tsens_sample::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TSENS_SAMPLE_SPEC;
impl crate::RegisterSpec for TSENS_SAMPLE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tsens_sample::R`](R) reader structure"]
impl crate::Readable for TSENS_SAMPLE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tsens_sample::W`](W) writer structure"]
impl crate::Writable for TSENS_SAMPLE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TSENS_SAMPLE to value 0x14"]
impl crate::Resettable for TSENS_SAMPLE_SPEC {
    const RESET_VALUE: u32 = 0x14;
}
