#[doc = "Register `OUT0_DO` reader"]
pub type R = crate::R<Out0DoSpec>;
#[doc = "Field `OUT0_DO` reader - DAC_OUT0 data output"]
pub type Out0DoR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:11 - DAC_OUT0 data output"]
    #[inline(always)]
    pub fn out0_do(&self) -> Out0DoR {
        Out0DoR::new((self.bits & 0x0fff) as u16)
    }
}
#[doc = "DAC_OUT0 data output register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`out0_do::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Out0DoSpec;
impl crate::RegisterSpec for Out0DoSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`out0_do::R`](R) reader structure"]
impl crate::Readable for Out0DoSpec {}
#[doc = "`reset()` method sets OUT0_DO to value 0"]
impl crate::Resettable for Out0DoSpec {
    const RESET_VALUE: u32 = 0;
}
