#[doc = "Register `MXINT%s_PRI` reader"]
pub type R = crate::R<MXINT_PRI_SPEC>;
#[doc = "Register `MXINT%s_PRI` writer"]
pub type W = crate::W<MXINT_PRI_SPEC>;
#[doc = "Field `CPU_MXINT_PRI` reader - "]
pub type CPU_MXINT_PRI_R = crate::FieldReader;
#[doc = "Field `CPU_MXINT_PRI` writer - "]
pub type CPU_MXINT_PRI_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn cpu_mxint_pri(&self) -> CPU_MXINT_PRI_R {
        CPU_MXINT_PRI_R::new((self.bits & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MXINT_PRI")
            .field("cpu_mxint_pri", &self.cpu_mxint_pri())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn cpu_mxint_pri(&mut self) -> CPU_MXINT_PRI_W<'_, MXINT_PRI_SPEC> {
        CPU_MXINT_PRI_W::new(self, 0)
    }
}
#[doc = "PLIC MX Interrupt %s Priority Register\n\nYou can [`read`](crate::Reg::read) this register and get [`mxint_pri::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mxint_pri::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MXINT_PRI_SPEC;
impl crate::RegisterSpec for MXINT_PRI_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mxint_pri::R`](R) reader structure"]
impl crate::Readable for MXINT_PRI_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mxint_pri::W`](W) writer structure"]
impl crate::Writable for MXINT_PRI_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MXINT%s_PRI to value 0"]
impl crate::Resettable for MXINT_PRI_SPEC {}
