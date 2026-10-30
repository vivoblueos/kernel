#[doc = "Register `RXON_DELAY` reader"]
pub type R = crate::R<RXON_DELAY_SPEC>;
#[doc = "Register `RXON_DELAY` writer"]
pub type W = crate::W<RXON_DELAY_SPEC>;
#[doc = "Field `RXON_DELAY` reader - "]
pub type RXON_DELAY_R = crate::FieldReader<u16>;
#[doc = "Field `RXON_DELAY` writer - "]
pub type RXON_DELAY_W<'a, REG> = crate::FieldWriter<'a, REG, 11, u16>;
impl R {
    #[doc = "Bits 0:10"]
    #[inline(always)]
    pub fn rxon_delay(&self) -> RXON_DELAY_R {
        RXON_DELAY_R::new((self.bits & 0x07ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RXON_DELAY")
            .field("rxon_delay", &self.rxon_delay())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:10"]
    #[inline(always)]
    pub fn rxon_delay(&mut self) -> RXON_DELAY_W<'_, RXON_DELAY_SPEC> {
        RXON_DELAY_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`rxon_delay::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rxon_delay::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RXON_DELAY_SPEC;
impl crate::RegisterSpec for RXON_DELAY_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rxon_delay::R`](R) reader structure"]
impl crate::Readable for RXON_DELAY_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rxon_delay::W`](W) writer structure"]
impl crate::Writable for RXON_DELAY_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RXON_DELAY to value 0"]
impl crate::Resettable for RXON_DELAY_SPEC {}
