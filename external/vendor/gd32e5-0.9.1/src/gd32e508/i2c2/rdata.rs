#[doc = "Register `RDATA` reader"]
pub type R = crate::R<RdataSpec>;
#[doc = "Field `RDATA` reader - Receive data value"]
pub type RdataR = crate::FieldReader;
impl R {
    #[doc = "Bits 0:7 - Receive data value"]
    #[inline(always)]
    pub fn rdata(&self) -> RdataR {
        RdataR::new((self.bits & 0xff) as u8)
    }
}
#[doc = "receive data register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rdata::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RdataSpec;
impl crate::RegisterSpec for RdataSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rdata::R`](R) reader structure"]
impl crate::Readable for RdataSpec {}
#[doc = "`reset()` method sets RDATA to value 0"]
impl crate::Resettable for RdataSpec {
    const RESET_VALUE: u32 = 0;
}
