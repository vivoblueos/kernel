#[doc = "Register `SLCINTVEC_TOHOST` writer"]
pub type W = crate::W<SLCINTVEC_TOHOST_SPEC>;
#[doc = "Field `SDIO_SLC0_TOHOST_INTVEC` writer - The interrupt set bit of SLCHOST_SLC0_TOHOST_BITn_INT (n: 0-7)."]
pub type SDIO_SLC0_TOHOST_INTVEC_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SDIO_SLC1_TOHOST_INTVEC` writer - The interrupt set bit of SLCHOST_SLC1_TOHOST_BITn_INT (n: 0-7)."]
pub type SDIO_SLC1_TOHOST_INTVEC_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SLCINTVEC_TOHOST_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bits 0:7 - The interrupt set bit of SLCHOST_SLC0_TOHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc0_tohost_intvec(
        &mut self,
    ) -> SDIO_SLC0_TOHOST_INTVEC_W<'_, SLCINTVEC_TOHOST_SPEC> {
        SDIO_SLC0_TOHOST_INTVEC_W::new(self, 0)
    }
    #[doc = "Bits 16:23 - The interrupt set bit of SLCHOST_SLC1_TOHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc1_tohost_intvec(
        &mut self,
    ) -> SDIO_SLC1_TOHOST_INTVEC_W<'_, SLCINTVEC_TOHOST_SPEC> {
        SDIO_SLC1_TOHOST_INTVEC_W::new(self, 16)
    }
}
#[doc = "Slave to host interrupt vector set\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slcintvec_tohost::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLCINTVEC_TOHOST_SPEC;
impl crate::RegisterSpec for SLCINTVEC_TOHOST_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`slcintvec_tohost::W`](W) writer structure"]
impl crate::Writable for SLCINTVEC_TOHOST_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLCINTVEC_TOHOST to value 0"]
impl crate::Resettable for SLCINTVEC_TOHOST_SPEC {}
