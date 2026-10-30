#[doc = "Register `UXINT%s_PRI` reader"]
pub type R = crate::R<UXINT_PRI_SPEC>;
#[doc = "Register `UXINT%s_PRI` writer"]
pub type W = crate::W<UXINT_PRI_SPEC>;
#[doc = "Field `CPU_UXINT_PRI` reader - "]
pub type CPU_UXINT_PRI_R = crate::FieldReader;
#[doc = "Field `CPU_UXINT_PRI` writer - "]
pub type CPU_UXINT_PRI_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn cpu_uxint_pri(&self) -> CPU_UXINT_PRI_R {
        CPU_UXINT_PRI_R::new((self.bits & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("UXINT_PRI")
            .field("cpu_uxint_pri", &self.cpu_uxint_pri())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn cpu_uxint_pri(&mut self) -> CPU_UXINT_PRI_W<'_, UXINT_PRI_SPEC> {
        CPU_UXINT_PRI_W::new(self, 0)
    }
}
#[doc = "PLIC UX Interrupt %s Priority Register\n\nYou can [`read`](crate::Reg::read) this register and get [`uxint_pri::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uxint_pri::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct UXINT_PRI_SPEC;
impl crate::RegisterSpec for UXINT_PRI_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`uxint_pri::R`](R) reader structure"]
impl crate::Readable for UXINT_PRI_SPEC {}
#[doc = "`write(|w| ..)` method takes [`uxint_pri::W`](W) writer structure"]
impl crate::Writable for UXINT_PRI_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets UXINT%s_PRI to value 0"]
impl crate::Resettable for UXINT_PRI_SPEC {}
