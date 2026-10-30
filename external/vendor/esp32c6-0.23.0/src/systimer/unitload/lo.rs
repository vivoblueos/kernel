#[doc = "Register `LO` reader"]
pub type R = crate::R<LO_SPEC>;
#[doc = "Register `LO` writer"]
pub type W = crate::W<LO_SPEC>;
#[doc = "Field `LOAD_LO` reader - timer unit0 load low 32 bits"]
pub type LOAD_LO_R = crate::FieldReader<u32>;
#[doc = "Field `LOAD_LO` writer - timer unit0 load low 32 bits"]
pub type LOAD_LO_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32, crate::Safe>;
impl R {
    #[doc = "Bits 0:31 - timer unit0 load low 32 bits"]
    #[inline(always)]
    pub fn load_lo(&self) -> LOAD_LO_R {
        LOAD_LO_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LO")
            .field("load_lo", &self.load_lo())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - timer unit0 load low 32 bits"]
    #[inline(always)]
    pub fn load_lo(&mut self) -> LOAD_LO_W<'_, LO_SPEC> {
        LOAD_LO_W::new(self, 0)
    }
}
#[doc = "system timer unit0 value low load register\n\nYou can [`read`](crate::Reg::read) this register and get [`lo::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lo::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
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
