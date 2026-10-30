#[doc = "Register `DMA_START` writer"]
pub type W = crate::W<DMA_START_SPEC>;
#[doc = "Field `DMA_START` writer - Start dma-sha."]
pub type DMA_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<DMA_START_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Start dma-sha."]
    #[inline(always)]
    pub fn dma_start(&mut self) -> DMA_START_W<'_, DMA_START_SPEC> {
        DMA_START_W::new(self, 0)
    }
}
#[doc = "DMA configuration register 1.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_start::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DMA_START_SPEC;
impl crate::RegisterSpec for DMA_START_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`dma_start::W`](W) writer structure"]
impl crate::Writable for DMA_START_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DMA_START to value 0"]
impl crate::Resettable for DMA_START_SPEC {}
