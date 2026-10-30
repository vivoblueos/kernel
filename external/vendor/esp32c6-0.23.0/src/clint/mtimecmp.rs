#[doc = "Register `MTIMECMP` reader"]
pub type R = crate::R<MTIMECMP_SPEC>;
#[doc = "Register `MTIMECMP` writer"]
pub type W = crate::W<MTIMECMP_SPEC>;
#[doc = "Field `MTIMECMP` reader - Configures the 64-bit machine timer compare value."]
pub type MTIMECMP_R = crate::FieldReader<u64>;
#[doc = "Field `MTIMECMP` writer - Configures the 64-bit machine timer compare value."]
pub type MTIMECMP_W<'a, REG> = crate::FieldWriter<'a, REG, 64, u64>;
impl R {
    #[doc = "Bits 0:63 - Configures the 64-bit machine timer compare value."]
    #[inline(always)]
    pub fn mtimecmp(&self) -> MTIMECMP_R {
        MTIMECMP_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MTIMECMP")
            .field("mtimecmp", &self.mtimecmp())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:63 - Configures the 64-bit machine timer compare value."]
    #[inline(always)]
    pub fn mtimecmp(&mut self) -> MTIMECMP_W<'_, MTIMECMP_SPEC> {
        MTIMECMP_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`mtimecmp::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mtimecmp::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MTIMECMP_SPEC;
impl crate::RegisterSpec for MTIMECMP_SPEC {
    type Ux = u64;
}
#[doc = "`read()` method returns [`mtimecmp::R`](R) reader structure"]
impl crate::Readable for MTIMECMP_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mtimecmp::W`](W) writer structure"]
impl crate::Writable for MTIMECMP_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MTIMECMP to value 0"]
impl crate::Resettable for MTIMECMP_SPEC {}
