#[doc = "Register `MXINT_THRESH` reader"]
pub type R = crate::R<MXINT_THRESH_SPEC>;
#[doc = "Register `MXINT_THRESH` writer"]
pub type W = crate::W<MXINT_THRESH_SPEC>;
#[doc = "Field `CPU_MXINT_THRESH` reader - "]
pub type CPU_MXINT_THRESH_R = crate::FieldReader;
#[doc = "Field `CPU_MXINT_THRESH` writer - "]
pub type CPU_MXINT_THRESH_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7"]
    #[inline(always)]
    pub fn cpu_mxint_thresh(&self) -> CPU_MXINT_THRESH_R {
        CPU_MXINT_THRESH_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MXINT_THRESH")
            .field("cpu_mxint_thresh", &self.cpu_mxint_thresh())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7"]
    #[inline(always)]
    pub fn cpu_mxint_thresh(&mut self) -> CPU_MXINT_THRESH_W<'_, MXINT_THRESH_SPEC> {
        CPU_MXINT_THRESH_W::new(self, 0)
    }
}
#[doc = "PLIC MX Interrupt Threshold Register\n\nYou can [`read`](crate::Reg::read) this register and get [`mxint_thresh::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mxint_thresh::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MXINT_THRESH_SPEC;
impl crate::RegisterSpec for MXINT_THRESH_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mxint_thresh::R`](R) reader structure"]
impl crate::Readable for MXINT_THRESH_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mxint_thresh::W`](W) writer structure"]
impl crate::Writable for MXINT_THRESH_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MXINT_THRESH to value 0"]
impl crate::Resettable for MXINT_THRESH_SPEC {}
