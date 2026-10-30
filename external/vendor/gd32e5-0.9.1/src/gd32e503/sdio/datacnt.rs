#[doc = "Register `DATACNT` reader"]
pub type R = crate::R<DatacntSpec>;
#[doc = "Field `DATACNT` reader - Data count value"]
pub type DatacntR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:24 - Data count value"]
    #[inline(always)]
    pub fn datacnt(&self) -> DatacntR {
        DatacntR::new(self.bits & 0x01ff_ffff)
    }
}
#[doc = "Data counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`datacnt::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DatacntSpec;
impl crate::RegisterSpec for DatacntSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`datacnt::R`](R) reader structure"]
impl crate::Readable for DatacntSpec {}
#[doc = "`reset()` method sets DATACNT to value 0"]
impl crate::Resettable for DatacntSpec {
    const RESET_VALUE: u32 = 0;
}
