#[doc = "Register `ICACHE_PRELOAD_SIZE` reader"]
pub type R = crate::R<ICACHE_PRELOAD_SIZE_SPEC>;
#[doc = "Register `ICACHE_PRELOAD_SIZE` writer"]
pub type W = crate::W<ICACHE_PRELOAD_SIZE_SPEC>;
#[doc = "Field `ICACHE_PRELOAD_SIZE` reader - The bits are used to configure the length for preload operation. The bits are the counts of cache block. It should be combined with ICACHE_PRELOAD_ADDR_REG.."]
pub type ICACHE_PRELOAD_SIZE_R = crate::FieldReader<u16>;
#[doc = "Field `ICACHE_PRELOAD_SIZE` writer - The bits are used to configure the length for preload operation. The bits are the counts of cache block. It should be combined with ICACHE_PRELOAD_ADDR_REG.."]
pub type ICACHE_PRELOAD_SIZE_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - The bits are used to configure the length for preload operation. The bits are the counts of cache block. It should be combined with ICACHE_PRELOAD_ADDR_REG.."]
    #[inline(always)]
    pub fn icache_preload_size(&self) -> ICACHE_PRELOAD_SIZE_R {
        ICACHE_PRELOAD_SIZE_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ICACHE_PRELOAD_SIZE")
            .field("icache_preload_size", &self.icache_preload_size())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - The bits are used to configure the length for preload operation. The bits are the counts of cache block. It should be combined with ICACHE_PRELOAD_ADDR_REG.."]
    #[inline(always)]
    pub fn icache_preload_size(&mut self) -> ICACHE_PRELOAD_SIZE_W<'_, ICACHE_PRELOAD_SIZE_SPEC> {
        ICACHE_PRELOAD_SIZE_W::new(self, 0)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_preload_size::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_preload_size::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ICACHE_PRELOAD_SIZE_SPEC;
impl crate::RegisterSpec for ICACHE_PRELOAD_SIZE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`icache_preload_size::R`](R) reader structure"]
impl crate::Readable for ICACHE_PRELOAD_SIZE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`icache_preload_size::W`](W) writer structure"]
impl crate::Writable for ICACHE_PRELOAD_SIZE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ICACHE_PRELOAD_SIZE to value 0"]
impl crate::Resettable for ICACHE_PRELOAD_SIZE_SPEC {}
