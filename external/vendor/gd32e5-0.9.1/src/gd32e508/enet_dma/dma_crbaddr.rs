#[doc = "Register `DMA_CRBADDR` reader"]
pub type R = crate::R<DmaCrbaddrSpec>;
#[doc = "Field `RBAP` reader - receive buffer address pointer"]
pub type RbapR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - receive buffer address pointer"]
    #[inline(always)]
    pub fn rbap(&self) -> RbapR {
        RbapR::new(self.bits)
    }
}
#[doc = "Ethernet DMA current receive buffer address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_crbaddr::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DmaCrbaddrSpec;
impl crate::RegisterSpec for DmaCrbaddrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_crbaddr::R`](R) reader structure"]
impl crate::Readable for DmaCrbaddrSpec {}
#[doc = "`reset()` method sets DMA_CRBADDR to value 0"]
impl crate::Resettable for DmaCrbaddrSpec {
    const RESET_VALUE: u32 = 0;
}
