#[doc = "Register `UXINT_THRESH` reader"]
pub type R = crate::R<UXINT_THRESH_SPEC>;
#[doc = "Register `UXINT_THRESH` writer"]
pub type W = crate::W<UXINT_THRESH_SPEC>;
#[doc = "Field `CPU_UXINT_THRESH` reader - "]
pub type CPU_UXINT_THRESH_R = crate::FieldReader;
#[doc = "Field `CPU_UXINT_THRESH` writer - "]
pub type CPU_UXINT_THRESH_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7"]
    #[inline(always)]
    pub fn cpu_uxint_thresh(&self) -> CPU_UXINT_THRESH_R {
        CPU_UXINT_THRESH_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("UXINT_THRESH")
            .field("cpu_uxint_thresh", &self.cpu_uxint_thresh())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7"]
    #[inline(always)]
    pub fn cpu_uxint_thresh(&mut self) -> CPU_UXINT_THRESH_W<'_, UXINT_THRESH_SPEC> {
        CPU_UXINT_THRESH_W::new(self, 0)
    }
}
#[doc = "PLIC UX Interrupt Threshold Register\n\nYou can [`read`](crate::Reg::read) this register and get [`uxint_thresh::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uxint_thresh::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct UXINT_THRESH_SPEC;
impl crate::RegisterSpec for UXINT_THRESH_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`uxint_thresh::R`](R) reader structure"]
impl crate::Readable for UXINT_THRESH_SPEC {}
#[doc = "`write(|w| ..)` method takes [`uxint_thresh::W`](W) writer structure"]
impl crate::Writable for UXINT_THRESH_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets UXINT_THRESH to value 0"]
impl crate::Resettable for UXINT_THRESH_SPEC {}
