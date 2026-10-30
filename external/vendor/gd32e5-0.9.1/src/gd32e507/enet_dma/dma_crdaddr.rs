#[doc = "Register `DMA_CRDADDR` reader"]
pub type R = crate::R<DmaCrdaddrSpec>;
#[doc = "Field `RDAP` reader - Receive descriptor address pointer"]
pub type RdapR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Receive descriptor address pointer"]
    #[inline(always)]
    pub fn rdap(&self) -> RdapR {
        RdapR::new(self.bits)
    }
}
#[doc = "Ethernet DMA current receive descriptor address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_crdaddr::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DmaCrdaddrSpec;
impl crate::RegisterSpec for DmaCrdaddrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_crdaddr::R`](R) reader structure"]
impl crate::Readable for DmaCrdaddrSpec {}
#[doc = "`reset()` method sets DMA_CRDADDR to value 0"]
impl crate::Resettable for DmaCrdaddrSpec {
    const RESET_VALUE: u32 = 0;
}
