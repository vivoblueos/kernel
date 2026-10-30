#[doc = "Register `UXINT_TYPE` reader"]
pub type R = crate::R<UXINT_TYPE_SPEC>;
#[doc = "Register `UXINT_TYPE` writer"]
pub type W = crate::W<UXINT_TYPE_SPEC>;
#[doc = "Field `CPU_UXINT_TYPE` reader - "]
pub type CPU_UXINT_TYPE_R = crate::FieldReader<u32>;
#[doc = "Field `CPU_UXINT_TYPE` writer - "]
pub type CPU_UXINT_TYPE_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn cpu_uxint_type(&self) -> CPU_UXINT_TYPE_R {
        CPU_UXINT_TYPE_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("UXINT_TYPE")
            .field("cpu_uxint_type", &self.cpu_uxint_type())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn cpu_uxint_type(&mut self) -> CPU_UXINT_TYPE_W<'_, UXINT_TYPE_SPEC> {
        CPU_UXINT_TYPE_W::new(self, 0)
    }
}
#[doc = "PLIC UX Interrupt Type Register\n\nYou can [`read`](crate::Reg::read) this register and get [`uxint_type::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uxint_type::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct UXINT_TYPE_SPEC;
impl crate::RegisterSpec for UXINT_TYPE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`uxint_type::R`](R) reader structure"]
impl crate::Readable for UXINT_TYPE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`uxint_type::W`](W) writer structure"]
impl crate::Writable for UXINT_TYPE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets UXINT_TYPE to value 0"]
impl crate::Resettable for UXINT_TYPE_SPEC {}
