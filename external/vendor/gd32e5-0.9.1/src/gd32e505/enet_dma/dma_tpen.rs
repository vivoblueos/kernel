#[doc = "Register `DMA_TPEN` reader"]
pub type R = crate::R<DmaTpenSpec>;
#[doc = "Register `DMA_TPEN` writer"]
pub type W = crate::W<DmaTpenSpec>;
#[doc = "Field `TPE` reader - Transmit poll enable"]
pub type TpeR = crate::FieldReader<u32>;
#[doc = "Field `TPE` writer - Transmit poll enable"]
pub type TpeW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Transmit poll enable"]
    #[inline(always)]
    pub fn tpe(&self) -> TpeR {
        TpeR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - Transmit poll enable"]
    #[inline(always)]
    #[must_use]
    pub fn tpe(&mut self) -> TpeW<DmaTpenSpec> {
        TpeW::new(self, 0)
    }
}
#[doc = "Ethernet DMA transmit poll enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_tpen::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_tpen::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DmaTpenSpec;
impl crate::RegisterSpec for DmaTpenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_tpen::R`](R) reader structure"]
impl crate::Readable for DmaTpenSpec {}
#[doc = "`write(|w| ..)` method takes [`dma_tpen::W`](W) writer structure"]
impl crate::Writable for DmaTpenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DMA_TPEN to value 0"]
impl crate::Resettable for DmaTpenSpec {
    const RESET_VALUE: u32 = 0;
}
