#[doc = "Register `DMA_RPEN` reader"]
pub type R = crate::R<DmaRpenSpec>;
#[doc = "Register `DMA_RPEN` writer"]
pub type W = crate::W<DmaRpenSpec>;
#[doc = "Field `RPE` reader - Receive poll enable"]
pub type RpeR = crate::FieldReader<u32>;
#[doc = "Field `RPE` writer - Receive poll enable"]
pub type RpeW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Receive poll enable"]
    #[inline(always)]
    pub fn rpe(&self) -> RpeR {
        RpeR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - Receive poll enable"]
    #[inline(always)]
    #[must_use]
    pub fn rpe(&mut self) -> RpeW<DmaRpenSpec> {
        RpeW::new(self, 0)
    }
}
#[doc = "Ethernet DMA receive poll enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_rpen::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_rpen::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DmaRpenSpec;
impl crate::RegisterSpec for DmaRpenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_rpen::R`](R) reader structure"]
impl crate::Readable for DmaRpenSpec {}
#[doc = "`write(|w| ..)` method takes [`dma_rpen::W`](W) writer structure"]
impl crate::Writable for DmaRpenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DMA_RPEN to value 0"]
impl crate::Resettable for DmaRpenSpec {
    const RESET_VALUE: u32 = 0;
}
