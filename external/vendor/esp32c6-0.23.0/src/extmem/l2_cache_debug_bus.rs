#[doc = "Register `L2_CACHE_DEBUG_BUS` reader"]
pub type R = crate::R<L2_CACHE_DEBUG_BUS_SPEC>;
#[doc = "Field `L2_CACHE_DEBUG_BUS` reader - This is a constant place where we can write data to or read data from the tag/data memory on the specified cache."]
pub type L2_CACHE_DEBUG_BUS_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - This is a constant place where we can write data to or read data from the tag/data memory on the specified cache."]
    #[inline(always)]
    pub fn l2_cache_debug_bus(&self) -> L2_CACHE_DEBUG_BUS_R {
        L2_CACHE_DEBUG_BUS_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L2_CACHE_DEBUG_BUS")
            .field("l2_cache_debug_bus", &self.l2_cache_debug_bus())
            .finish()
    }
}
#[doc = "Cache Tag/data memory content register\n\nYou can [`read`](crate::Reg::read) this register and get [`l2_cache_debug_bus::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L2_CACHE_DEBUG_BUS_SPEC;
impl crate::RegisterSpec for L2_CACHE_DEBUG_BUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l2_cache_debug_bus::R`](R) reader structure"]
impl crate::Readable for L2_CACHE_DEBUG_BUS_SPEC {}
#[doc = "`reset()` method sets L2_CACHE_DEBUG_BUS to value 0x03a4"]
impl crate::Resettable for L2_CACHE_DEBUG_BUS_SPEC {
    const RESET_VALUE: u32 = 0x03a4;
}
