#[doc = "Register `LOADLO` reader"]
pub type R = crate::R<LOADLO_SPEC>;
#[doc = "Register `LOADLO` writer"]
pub type W = crate::W<LOADLO_SPEC>;
#[doc = "Field `LOAD_LO` reader - Low 32 bits of the value that a reload will load onto timer %s time-base Counter."]
pub type LOAD_LO_R = crate::FieldReader<u32>;
#[doc = "Field `LOAD_LO` writer - Low 32 bits of the value that a reload will load onto timer %s time-base Counter."]
pub type LOAD_LO_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Low 32 bits of the value that a reload will load onto timer %s time-base Counter."]
    #[inline(always)]
    pub fn load_lo(&self) -> LOAD_LO_R {
        LOAD_LO_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LOADLO")
            .field("load_lo", &self.load_lo())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Low 32 bits of the value that a reload will load onto timer %s time-base Counter."]
    #[inline(always)]
    pub fn load_lo(&mut self) -> LOAD_LO_W<'_, LOADLO_SPEC> {
        LOAD_LO_W::new(self, 0)
    }
}
#[doc = "Timer %s reload value, low 32 bits\n\nYou can [`read`](crate::Reg::read) this register and get [`loadlo::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`loadlo::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LOADLO_SPEC;
impl crate::RegisterSpec for LOADLO_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`loadlo::R`](R) reader structure"]
impl crate::Readable for LOADLO_SPEC {}
#[doc = "`write(|w| ..)` method takes [`loadlo::W`](W) writer structure"]
impl crate::Writable for LOADLO_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LOADLO to value 0"]
impl crate::Resettable for LOADLO_SPEC {}
