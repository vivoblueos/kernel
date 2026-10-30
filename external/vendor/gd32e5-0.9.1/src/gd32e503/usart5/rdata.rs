#[doc = "Register `RDATA` reader"]
pub type R = crate::R<RdataSpec>;
#[doc = "Field `RDATA` reader - Receive Data value"]
pub type RdataR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:8 - Receive Data value"]
    #[inline(always)]
    pub fn rdata(&self) -> RdataR {
        RdataR::new((self.bits & 0x01ff) as u16)
    }
}
#[doc = "Receive data register (\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rdata::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
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
