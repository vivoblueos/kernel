#[doc = "Register `MXINT_TYPE` reader"]
pub type R = crate::R<MXINT_TYPE_SPEC>;
#[doc = "Register `MXINT_TYPE` writer"]
pub type W = crate::W<MXINT_TYPE_SPEC>;
#[doc = "Field `CPU_MXINT_TYPE` reader - "]
pub type CPU_MXINT_TYPE_R = crate::FieldReader<u32>;
#[doc = "Field `CPU_MXINT_TYPE` writer - "]
pub type CPU_MXINT_TYPE_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn cpu_mxint_type(&self) -> CPU_MXINT_TYPE_R {
        CPU_MXINT_TYPE_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MXINT_TYPE")
            .field("cpu_mxint_type", &self.cpu_mxint_type())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn cpu_mxint_type(&mut self) -> CPU_MXINT_TYPE_W<'_, MXINT_TYPE_SPEC> {
        CPU_MXINT_TYPE_W::new(self, 0)
    }
}
#[doc = "PLIC MX Interrupt Type Register\n\nYou can [`read`](crate::Reg::read) this register and get [`mxint_type::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mxint_type::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MXINT_TYPE_SPEC;
impl crate::RegisterSpec for MXINT_TYPE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mxint_type::R`](R) reader structure"]
impl crate::Readable for MXINT_TYPE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mxint_type::W`](W) writer structure"]
impl crate::Writable for MXINT_TYPE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MXINT_TYPE to value 0"]
impl crate::Resettable for MXINT_TYPE_SPEC {}
