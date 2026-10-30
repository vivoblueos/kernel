#[doc = "Register `LO` reader"]
pub type R = crate::R<LO_SPEC>;
#[doc = "Register `LO` writer"]
pub type W = crate::W<LO_SPEC>;
#[doc = "Field `LO` reader - timer taget0 low 32 bit"]
pub type LO_R = crate::FieldReader<u32>;
#[doc = "Field `LO` writer - timer taget0 low 32 bit"]
pub type LO_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32, crate::Safe>;
impl R {
    #[doc = "Bits 0:31 - timer taget0 low 32 bit"]
    #[inline(always)]
    pub fn lo(&self) -> LO_R {
        LO_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LO").field("lo", &self.lo()).finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - timer taget0 low 32 bit"]
    #[inline(always)]
    pub fn lo(&mut self) -> LO_W<'_, LO_SPEC> {
        LO_W::new(self, 0)
    }
}
#[doc = "SYSTIMER_TARGET0_LO.\n\nYou can [`read`](crate::Reg::read) this register and get [`lo::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lo::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LO_SPEC;
impl crate::RegisterSpec for LO_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lo::R`](R) reader structure"]
impl crate::Readable for LO_SPEC {}
#[doc = "`write(|w| ..)` method takes [`lo::W`](W) writer structure"]
impl crate::Writable for LO_SPEC {
    type Safety = crate::Safe;
}
#[doc = "`reset()` method sets LO to value 0"]
impl crate::Resettable for LO_SPEC {}
