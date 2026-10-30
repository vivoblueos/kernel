#[doc = "Register `MSC_RFCECNT` reader"]
pub type R = crate::R<MscRfcecntSpec>;
#[doc = "Field `RFCER` reader - Received frames with CRC error counter"]
pub type RfcerR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Received frames with CRC error counter"]
    #[inline(always)]
    pub fn rfcer(&self) -> RfcerR {
        RfcerR::new(self.bits)
    }
}
#[doc = "Ethernet MSC received frames with CRC error counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_rfcecnt::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MscRfcecntSpec;
impl crate::RegisterSpec for MscRfcecntSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`msc_rfcecnt::R`](R) reader structure"]
impl crate::Readable for MscRfcecntSpec {}
#[doc = "`reset()` method sets MSC_RFCECNT to value 0"]
impl crate::Resettable for MscRfcecntSpec {
    const RESET_VALUE: u32 = 0;
}
