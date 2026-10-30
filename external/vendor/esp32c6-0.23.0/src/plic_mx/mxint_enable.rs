#[doc = "Register `MXINT_ENABLE` reader"]
pub type R = crate::R<MXINT_ENABLE_SPEC>;
#[doc = "Register `MXINT_ENABLE` writer"]
pub type W = crate::W<MXINT_ENABLE_SPEC>;
#[doc = "Field `CPU_MXINT_ENABLE` reader - "]
pub type CPU_MXINT_ENABLE_R = crate::FieldReader<u32>;
#[doc = "Field `CPU_MXINT_ENABLE` writer - "]
pub type CPU_MXINT_ENABLE_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn cpu_mxint_enable(&self) -> CPU_MXINT_ENABLE_R {
        CPU_MXINT_ENABLE_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MXINT_ENABLE")
            .field("cpu_mxint_enable", &self.cpu_mxint_enable())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn cpu_mxint_enable(&mut self) -> CPU_MXINT_ENABLE_W<'_, MXINT_ENABLE_SPEC> {
        CPU_MXINT_ENABLE_W::new(self, 0)
    }
}
#[doc = "PLIC MX Interrupt Enable Register\n\nYou can [`read`](crate::Reg::read) this register and get [`mxint_enable::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mxint_enable::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MXINT_ENABLE_SPEC;
impl crate::RegisterSpec for MXINT_ENABLE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mxint_enable::R`](R) reader structure"]
impl crate::Readable for MXINT_ENABLE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mxint_enable::W`](W) writer structure"]
impl crate::Writable for MXINT_ENABLE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MXINT_ENABLE to value 0"]
impl crate::Resettable for MXINT_ENABLE_SPEC {}
