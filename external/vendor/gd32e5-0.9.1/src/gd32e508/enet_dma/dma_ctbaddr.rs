#[doc = "Register `DMA_CTBADDR` reader"]
pub type R = crate::R<DmaCtbaddrSpec>;
#[doc = "Field `TBAP` reader - Transmit buffer address pointer"]
pub type TbapR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Transmit buffer address pointer"]
    #[inline(always)]
    pub fn tbap(&self) -> TbapR {
        TbapR::new(self.bits)
    }
}
#[doc = "Ethernet DMA current transmit buffer address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_ctbaddr::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DmaCtbaddrSpec;
impl crate::RegisterSpec for DmaCtbaddrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_ctbaddr::R`](R) reader structure"]
impl crate::Readable for DmaCtbaddrSpec {}
#[doc = "`reset()` method sets DMA_CTBADDR to value 0"]
impl crate::Resettable for DmaCtbaddrSpec {
    const RESET_VALUE: u32 = 0;
}
