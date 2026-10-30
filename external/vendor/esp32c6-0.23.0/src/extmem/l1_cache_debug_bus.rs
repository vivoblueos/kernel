#[doc = "Register `L1_CACHE_DEBUG_BUS` reader"]
pub type R = crate::R<L1_CACHE_DEBUG_BUS_SPEC>;
#[doc = "Register `L1_CACHE_DEBUG_BUS` writer"]
pub type W = crate::W<L1_CACHE_DEBUG_BUS_SPEC>;
#[doc = "Field `L1_CACHE_DEBUG_BUS` reader - This is a constant place where we can write data to or read data from the tag/data memory on the specified cache."]
pub type L1_CACHE_DEBUG_BUS_R = crate::FieldReader<u32>;
#[doc = "Field `L1_CACHE_DEBUG_BUS` writer - This is a constant place where we can write data to or read data from the tag/data memory on the specified cache."]
pub type L1_CACHE_DEBUG_BUS_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - This is a constant place where we can write data to or read data from the tag/data memory on the specified cache."]
    #[inline(always)]
    pub fn l1_cache_debug_bus(&self) -> L1_CACHE_DEBUG_BUS_R {
        L1_CACHE_DEBUG_BUS_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_DEBUG_BUS")
            .field("l1_cache_debug_bus", &self.l1_cache_debug_bus())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - This is a constant place where we can write data to or read data from the tag/data memory on the specified cache."]
    #[inline(always)]
    pub fn l1_cache_debug_bus(&mut self) -> L1_CACHE_DEBUG_BUS_W<'_, L1_CACHE_DEBUG_BUS_SPEC> {
        L1_CACHE_DEBUG_BUS_W::new(self, 0)
    }
}
#[doc = "Cache Tag/data memory content register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_debug_bus::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`l1_cache_debug_bus::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_DEBUG_BUS_SPEC;
impl crate::RegisterSpec for L1_CACHE_DEBUG_BUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_debug_bus::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_DEBUG_BUS_SPEC {}
#[doc = "`write(|w| ..)` method takes [`l1_cache_debug_bus::W`](W) writer structure"]
impl crate::Writable for L1_CACHE_DEBUG_BUS_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets L1_CACHE_DEBUG_BUS to value 0x0254"]
impl crate::Resettable for L1_CACHE_DEBUG_BUS_SPEC {
    const RESET_VALUE: u32 = 0x0254;
}
