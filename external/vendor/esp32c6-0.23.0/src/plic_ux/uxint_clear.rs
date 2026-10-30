#[doc = "Register `UXINT_CLEAR` reader"]
pub type R = crate::R<UXINT_CLEAR_SPEC>;
#[doc = "Register `UXINT_CLEAR` writer"]
pub type W = crate::W<UXINT_CLEAR_SPEC>;
#[doc = "Field `CPU_UXINT_CLEAR` reader - "]
pub type CPU_UXINT_CLEAR_R = crate::FieldReader<u32>;
#[doc = "Field `CPU_UXINT_CLEAR` writer - "]
pub type CPU_UXINT_CLEAR_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn cpu_uxint_clear(&self) -> CPU_UXINT_CLEAR_R {
        CPU_UXINT_CLEAR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("UXINT_CLEAR")
            .field("cpu_uxint_clear", &self.cpu_uxint_clear())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn cpu_uxint_clear(&mut self) -> CPU_UXINT_CLEAR_W<'_, UXINT_CLEAR_SPEC> {
        CPU_UXINT_CLEAR_W::new(self, 0)
    }
}
#[doc = "PLIC UX Interrupt Clear Register\n\nYou can [`read`](crate::Reg::read) this register and get [`uxint_clear::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uxint_clear::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct UXINT_CLEAR_SPEC;
impl crate::RegisterSpec for UXINT_CLEAR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`uxint_clear::R`](R) reader structure"]
impl crate::Readable for UXINT_CLEAR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`uxint_clear::W`](W) writer structure"]
impl crate::Writable for UXINT_CLEAR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets UXINT_CLEAR to value 0"]
impl crate::Resettable for UXINT_CLEAR_SPEC {}
