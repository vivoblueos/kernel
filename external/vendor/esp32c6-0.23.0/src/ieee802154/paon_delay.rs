#[doc = "Register `PAON_DELAY` reader"]
pub type R = crate::R<PAON_DELAY_SPEC>;
#[doc = "Register `PAON_DELAY` writer"]
pub type W = crate::W<PAON_DELAY_SPEC>;
#[doc = "Field `PAON_DELAY` reader - "]
pub type PAON_DELAY_R = crate::FieldReader<u16>;
#[doc = "Field `PAON_DELAY` writer - "]
pub type PAON_DELAY_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
impl R {
    #[doc = "Bits 0:9"]
    #[inline(always)]
    pub fn paon_delay(&self) -> PAON_DELAY_R {
        PAON_DELAY_R::new((self.bits & 0x03ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PAON_DELAY")
            .field("paon_delay", &self.paon_delay())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:9"]
    #[inline(always)]
    pub fn paon_delay(&mut self) -> PAON_DELAY_W<'_, PAON_DELAY_SPEC> {
        PAON_DELAY_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`paon_delay::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`paon_delay::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PAON_DELAY_SPEC;
impl crate::RegisterSpec for PAON_DELAY_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`paon_delay::R`](R) reader structure"]
impl crate::Readable for PAON_DELAY_SPEC {}
#[doc = "`write(|w| ..)` method takes [`paon_delay::W`](W) writer structure"]
impl crate::Writable for PAON_DELAY_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PAON_DELAY to value 0"]
impl crate::Resettable for PAON_DELAY_SPEC {}
