#[doc = "Register `DMA_BLOCK_NUM` reader"]
pub type R = crate::R<DMA_BLOCK_NUM_SPEC>;
#[doc = "Register `DMA_BLOCK_NUM` writer"]
pub type W = crate::W<DMA_BLOCK_NUM_SPEC>;
#[doc = "Field `DMA_BLOCK_NUM` reader - Dma-sha block number."]
pub type DMA_BLOCK_NUM_R = crate::FieldReader;
#[doc = "Field `DMA_BLOCK_NUM` writer - Dma-sha block number."]
pub type DMA_BLOCK_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
impl R {
    #[doc = "Bits 0:5 - Dma-sha block number."]
    #[inline(always)]
    pub fn dma_block_num(&self) -> DMA_BLOCK_NUM_R {
        DMA_BLOCK_NUM_R::new((self.bits & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DMA_BLOCK_NUM")
            .field("dma_block_num", &self.dma_block_num())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:5 - Dma-sha block number."]
    #[inline(always)]
    pub fn dma_block_num(&mut self) -> DMA_BLOCK_NUM_W<'_, DMA_BLOCK_NUM_SPEC> {
        DMA_BLOCK_NUM_W::new(self, 0)
    }
}
#[doc = "DMA configuration register 0.\n\nYou can [`read`](crate::Reg::read) this register and get [`dma_block_num::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_block_num::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DMA_BLOCK_NUM_SPEC;
impl crate::RegisterSpec for DMA_BLOCK_NUM_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_block_num::R`](R) reader structure"]
impl crate::Readable for DMA_BLOCK_NUM_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dma_block_num::W`](W) writer structure"]
impl crate::Writable for DMA_BLOCK_NUM_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DMA_BLOCK_NUM to value 0"]
impl crate::Resettable for DMA_BLOCK_NUM_SPEC {}
