#[doc = "Register `L2_CACHE_AUTOLOAD_SCT2_ADDR` reader"]
pub type R = crate::R<L2_CACHE_AUTOLOAD_SCT2_ADDR_SPEC>;
#[doc = "Field `L2_CACHE_AUTOLOAD_SCT2_ADDR` reader - Those bits are used to configure the start virtual address of the third section for autoload operation on L2-Cache. Note that it should be used together with L2_CACHE_AUTOLOAD_SCT2_SIZE and L2_CACHE_AUTOLOAD_SCT2_ENA."]
pub type L2_CACHE_AUTOLOAD_SCT2_ADDR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Those bits are used to configure the start virtual address of the third section for autoload operation on L2-Cache. Note that it should be used together with L2_CACHE_AUTOLOAD_SCT2_SIZE and L2_CACHE_AUTOLOAD_SCT2_ENA."]
    #[inline(always)]
    pub fn l2_cache_autoload_sct2_addr(&self) -> L2_CACHE_AUTOLOAD_SCT2_ADDR_R {
        L2_CACHE_AUTOLOAD_SCT2_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L2_CACHE_AUTOLOAD_SCT2_ADDR")
            .field(
                "l2_cache_autoload_sct2_addr",
                &self.l2_cache_autoload_sct2_addr(),
            )
            .finish()
    }
}
#[doc = "L2 Cache autoload section 2 address configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l2_cache_autoload_sct2_addr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L2_CACHE_AUTOLOAD_SCT2_ADDR_SPEC;
impl crate::RegisterSpec for L2_CACHE_AUTOLOAD_SCT2_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l2_cache_autoload_sct2_addr::R`](R) reader structure"]
impl crate::Readable for L2_CACHE_AUTOLOAD_SCT2_ADDR_SPEC {}
#[doc = "`reset()` method sets L2_CACHE_AUTOLOAD_SCT2_ADDR to value 0"]
impl crate::Resettable for L2_CACHE_AUTOLOAD_SCT2_ADDR_SPEC {}
