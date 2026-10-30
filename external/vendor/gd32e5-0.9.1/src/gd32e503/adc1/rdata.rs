#[doc = "Register `RDATA` reader"]
pub type R = crate::R<RdataSpec>;
#[doc = "Field `RDATA` reader - Regular channel data"]
pub type RdataR = crate::FieldReader<u16>;
#[doc = "Field `ADC1RDTR` reader - ADCegular channel data"]
pub type Adc1rdtrR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - Regular channel data"]
    #[inline(always)]
    pub fn rdata(&self) -> RdataR {
        RdataR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:31 - ADCegular channel data"]
    #[inline(always)]
    pub fn adc1rdtr(&self) -> Adc1rdtrR {
        Adc1rdtrR::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
#[doc = "regular data register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rdata::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
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
