#[doc = "Register `DMA_MFBOCNT` reader"]
pub type R = crate::R<DmaMfbocntSpec>;
#[doc = "Field `MSFC` reader - Missed frames by the controller"]
pub type MsfcR = crate::FieldReader<u16>;
#[doc = "Field `MSFA` reader - Missed frames by the application"]
pub type MsfaR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - Missed frames by the controller"]
    #[inline(always)]
    pub fn msfc(&self) -> MsfcR {
        MsfcR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 17:27 - Missed frames by the application"]
    #[inline(always)]
    pub fn msfa(&self) -> MsfaR {
        MsfaR::new(((self.bits >> 17) & 0x07ff) as u16)
    }
}
#[doc = "Ethernet DMA missed frame and buffer overflow counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_mfbocnt::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DmaMfbocntSpec;
impl crate::RegisterSpec for DmaMfbocntSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_mfbocnt::R`](R) reader structure"]
impl crate::Readable for DmaMfbocntSpec {}
#[doc = "`reset()` method sets DMA_MFBOCNT to value 0"]
impl crate::Resettable for DmaMfbocntSpec {
    const RESET_VALUE: u32 = 0;
}
