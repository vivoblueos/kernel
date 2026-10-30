#[doc = "Register `UTIMECMP` reader"]
pub type R = crate::R<UTIMECMP_SPEC>;
#[doc = "Register `UTIMECMP` writer"]
pub type W = crate::W<UTIMECMP_SPEC>;
#[doc = "Field `UTIMECMP` reader - Configures the 64-bit user timer compare value."]
pub type UTIMECMP_R = crate::FieldReader<u64>;
#[doc = "Field `UTIMECMP` writer - Configures the 64-bit user timer compare value."]
pub type UTIMECMP_W<'a, REG> = crate::FieldWriter<'a, REG, 64, u64>;
impl R {
    #[doc = "Bits 0:63 - Configures the 64-bit user timer compare value."]
    #[inline(always)]
    pub fn utimecmp(&self) -> UTIMECMP_R {
        UTIMECMP_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("UTIMECMP")
            .field("utimecmp", &self.utimecmp())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:63 - Configures the 64-bit user timer compare value."]
    #[inline(always)]
    pub fn utimecmp(&mut self) -> UTIMECMP_W<'_, UTIMECMP_SPEC> {
        UTIMECMP_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`utimecmp::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`utimecmp::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct UTIMECMP_SPEC;
impl crate::RegisterSpec for UTIMECMP_SPEC {
    type Ux = u64;
}
#[doc = "`read()` method returns [`utimecmp::R`](R) reader structure"]
impl crate::Readable for UTIMECMP_SPEC {}
#[doc = "`write(|w| ..)` method takes [`utimecmp::W`](W) writer structure"]
impl crate::Writable for UTIMECMP_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets UTIMECMP to value 0"]
impl crate::Resettable for UTIMECMP_SPEC {}
