#[doc = "Register `TXON_DELAY` reader"]
pub type R = crate::R<TXON_DELAY_SPEC>;
#[doc = "Register `TXON_DELAY` writer"]
pub type W = crate::W<TXON_DELAY_SPEC>;
#[doc = "Field `TXON_DELAY` reader - "]
pub type TXON_DELAY_R = crate::FieldReader<u16>;
#[doc = "Field `TXON_DELAY` writer - "]
pub type TXON_DELAY_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
impl R {
    #[doc = "Bits 0:9"]
    #[inline(always)]
    pub fn txon_delay(&self) -> TXON_DELAY_R {
        TXON_DELAY_R::new((self.bits & 0x03ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TXON_DELAY")
            .field("txon_delay", &self.txon_delay())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:9"]
    #[inline(always)]
    pub fn txon_delay(&mut self) -> TXON_DELAY_W<'_, TXON_DELAY_SPEC> {
        TXON_DELAY_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`txon_delay::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txon_delay::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TXON_DELAY_SPEC;
impl crate::RegisterSpec for TXON_DELAY_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`txon_delay::R`](R) reader structure"]
impl crate::Readable for TXON_DELAY_SPEC {}
#[doc = "`write(|w| ..)` method takes [`txon_delay::W`](W) writer structure"]
impl crate::Writable for TXON_DELAY_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TXON_DELAY to value 0"]
impl crate::Resettable for TXON_DELAY_SPEC {}
