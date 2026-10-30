#[doc = "Register `TXOFF_DELAY` reader"]
pub type R = crate::R<TXOFF_DELAY_SPEC>;
#[doc = "Register `TXOFF_DELAY` writer"]
pub type W = crate::W<TXOFF_DELAY_SPEC>;
#[doc = "Field `TXOFF_DELAY` reader - "]
pub type TXOFF_DELAY_R = crate::FieldReader;
#[doc = "Field `TXOFF_DELAY` writer - "]
pub type TXOFF_DELAY_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
impl R {
    #[doc = "Bits 0:5"]
    #[inline(always)]
    pub fn txoff_delay(&self) -> TXOFF_DELAY_R {
        TXOFF_DELAY_R::new((self.bits & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TXOFF_DELAY")
            .field("txoff_delay", &self.txoff_delay())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:5"]
    #[inline(always)]
    pub fn txoff_delay(&mut self) -> TXOFF_DELAY_W<'_, TXOFF_DELAY_SPEC> {
        TXOFF_DELAY_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`txoff_delay::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txoff_delay::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TXOFF_DELAY_SPEC;
impl crate::RegisterSpec for TXOFF_DELAY_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`txoff_delay::R`](R) reader structure"]
impl crate::Readable for TXOFF_DELAY_SPEC {}
#[doc = "`write(|w| ..)` method takes [`txoff_delay::W`](W) writer structure"]
impl crate::Writable for TXOFF_DELAY_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TXOFF_DELAY to value 0"]
impl crate::Resettable for TXOFF_DELAY_SPEC {}
