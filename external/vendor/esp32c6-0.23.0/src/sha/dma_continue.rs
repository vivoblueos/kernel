#[doc = "Register `DMA_CONTINUE` writer"]
pub type W = crate::W<DMA_CONTINUE_SPEC>;
#[doc = "Field `DMA_CONTINUE` writer - Continue dma-sha."]
pub type DMA_CONTINUE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<DMA_CONTINUE_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Continue dma-sha."]
    #[inline(always)]
    pub fn dma_continue(&mut self) -> DMA_CONTINUE_W<'_, DMA_CONTINUE_SPEC> {
        DMA_CONTINUE_W::new(self, 0)
    }
}
#[doc = "DMA configuration register 2.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_continue::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DMA_CONTINUE_SPEC;
impl crate::RegisterSpec for DMA_CONTINUE_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`dma_continue::W`](W) writer structure"]
impl crate::Writable for DMA_CONTINUE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DMA_CONTINUE to value 0"]
impl crate::Resettable for DMA_CONTINUE_SPEC {}
