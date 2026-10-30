#[doc = "Register `PID` reader"]
pub type R = crate::R<PidSpec>;
#[doc = "Field `PID` reader - Product reserved ID code register"]
pub type PidR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Product reserved ID code register"]
    #[inline(always)]
    pub fn pid(&self) -> PidR {
        PidR::new(self.bits)
    }
}
#[doc = "Product ID register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pid::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PidSpec;
impl crate::RegisterSpec for PidSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pid::R`](R) reader structure"]
impl crate::Readable for PidSpec {}
#[doc = "`reset()` method sets PID to value 0"]
impl crate::Resettable for PidSpec {
    const RESET_VALUE: u32 = 0;
}
