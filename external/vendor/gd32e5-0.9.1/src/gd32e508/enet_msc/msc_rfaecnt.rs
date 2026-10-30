#[doc = "Register `MSC_RFAECNT` reader"]
pub type R = crate::R<MscRfaecntSpec>;
#[doc = "Field `RFAER` reader - Received frames with alignment error counter"]
pub type RfaerR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Received frames with alignment error counter"]
    #[inline(always)]
    pub fn rfaer(&self) -> RfaerR {
        RfaerR::new(self.bits)
    }
}
#[doc = "Ethernet MSC received frames with alignment error counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_rfaecnt::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MscRfaecntSpec;
impl crate::RegisterSpec for MscRfaecntSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`msc_rfaecnt::R`](R) reader structure"]
impl crate::Readable for MscRfaecntSpec {}
#[doc = "`reset()` method sets MSC_RFAECNT to value 0"]
impl crate::Resettable for MscRfaecntSpec {
    const RESET_VALUE: u32 = 0;
}
