#[doc = "Register `REGDMA_CURRENT_LINK_ADDR` reader"]
pub type R = crate::R<REGDMA_CURRENT_LINK_ADDR_SPEC>;
#[doc = "Field `CURRENT_LINK_ADDR` reader - current link addr reg"]
pub type CURRENT_LINK_ADDR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - current link addr reg"]
    #[inline(always)]
    pub fn current_link_addr(&self) -> CURRENT_LINK_ADDR_R {
        CURRENT_LINK_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("REGDMA_CURRENT_LINK_ADDR")
            .field("current_link_addr", &self.current_link_addr())
            .finish()
    }
}
#[doc = "current link addr\n\nYou can [`read`](crate::Reg::read) this register and get [`regdma_current_link_addr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REGDMA_CURRENT_LINK_ADDR_SPEC;
impl crate::RegisterSpec for REGDMA_CURRENT_LINK_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`regdma_current_link_addr::R`](R) reader structure"]
impl crate::Readable for REGDMA_CURRENT_LINK_ADDR_SPEC {}
#[doc = "`reset()` method sets REGDMA_CURRENT_LINK_ADDR to value 0"]
impl crate::Resettable for REGDMA_CURRENT_LINK_ADDR_SPEC {}
