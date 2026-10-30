#[doc = "Register `DMA_EXIT` writer"]
pub type W = crate::W<DMA_EXIT_SPEC>;
#[doc = "Field `DMA_EXIT` writer - Set this register to leave calculation done stage. Recommend to use it after software finishes reading DMA's output buffer."]
pub type DMA_EXIT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<DMA_EXIT_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Set this register to leave calculation done stage. Recommend to use it after software finishes reading DMA's output buffer."]
    #[inline(always)]
    pub fn dma_exit(&mut self) -> DMA_EXIT_W<'_, DMA_EXIT_SPEC> {
        DMA_EXIT_W::new(self, 0)
    }
}
#[doc = "AES-DMA exit config\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_exit::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DMA_EXIT_SPEC;
impl crate::RegisterSpec for DMA_EXIT_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`dma_exit::W`](W) writer structure"]
impl crate::Writable for DMA_EXIT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DMA_EXIT to value 0"]
impl crate::Resettable for DMA_EXIT_SPEC {}
