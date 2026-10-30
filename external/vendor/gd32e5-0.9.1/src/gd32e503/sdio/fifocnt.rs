#[doc = "Register `FIFOCNT` reader"]
pub type R = crate::R<FifocntSpec>;
#[doc = "Field `FIFOCNT` reader - FIFO counter"]
pub type FifocntR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:23 - FIFO counter"]
    #[inline(always)]
    pub fn fifocnt(&self) -> FifocntR {
        FifocntR::new(self.bits & 0x00ff_ffff)
    }
}
#[doc = "FIFO counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fifocnt::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FifocntSpec;
impl crate::RegisterSpec for FifocntSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fifocnt::R`](R) reader structure"]
impl crate::Readable for FifocntSpec {}
#[doc = "`reset()` method sets FIFOCNT to value 0"]
impl crate::Resettable for FifocntSpec {
    const RESET_VALUE: u32 = 0;
}
