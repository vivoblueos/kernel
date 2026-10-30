#[doc = "Register `DMA_ENABLE` reader"]
pub type R = crate::R<DMA_ENABLE_SPEC>;
#[doc = "Register `DMA_ENABLE` writer"]
pub type W = crate::W<DMA_ENABLE_SPEC>;
#[doc = "Field `DMA_ENABLE` reader - 1'b0: typical AES working mode, 1'b1: DMA-AES working mode."]
pub type DMA_ENABLE_R = crate::BitReader;
#[doc = "Field `DMA_ENABLE` writer - 1'b0: typical AES working mode, 1'b1: DMA-AES working mode."]
pub type DMA_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - 1'b0: typical AES working mode, 1'b1: DMA-AES working mode."]
    #[inline(always)]
    pub fn dma_enable(&self) -> DMA_ENABLE_R {
        DMA_ENABLE_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DMA_ENABLE")
            .field("dma_enable", &self.dma_enable())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - 1'b0: typical AES working mode, 1'b1: DMA-AES working mode."]
    #[inline(always)]
    pub fn dma_enable(&mut self) -> DMA_ENABLE_W<'_, DMA_ENABLE_SPEC> {
        DMA_ENABLE_W::new(self, 0)
    }
}
#[doc = "DMA-AES working mode register\n\nYou can [`read`](crate::Reg::read) this register and get [`dma_enable::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_enable::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DMA_ENABLE_SPEC;
impl crate::RegisterSpec for DMA_ENABLE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_enable::R`](R) reader structure"]
impl crate::Readable for DMA_ENABLE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dma_enable::W`](W) writer structure"]
impl crate::Writable for DMA_ENABLE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DMA_ENABLE to value 0"]
impl crate::Resettable for DMA_ENABLE_SPEC {}
