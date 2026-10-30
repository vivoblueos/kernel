#[doc = "Register `DMA_CTDADDR` reader"]
pub type R = crate::R<DmaCtdaddrSpec>;
#[doc = "Field `TDAP` reader - transmit descriptor address pointer"]
pub type TdapR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - transmit descriptor address pointer"]
    #[inline(always)]
    pub fn tdap(&self) -> TdapR {
        TdapR::new(self.bits)
    }
}
#[doc = "DMA current transmit descriptor address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_ctdaddr::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DmaCtdaddrSpec;
impl crate::RegisterSpec for DmaCtdaddrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_ctdaddr::R`](R) reader structure"]
impl crate::Readable for DmaCtdaddrSpec {}
#[doc = "`reset()` method sets DMA_CTDADDR to value 0"]
impl crate::Resettable for DmaCtdaddrSpec {
    const RESET_VALUE: u32 = 0;
}
