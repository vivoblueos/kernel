#[doc = "Register `DIVH` reader"]
pub type R = crate::R<DivhSpec>;
#[doc = "Field `DIV` reader - RTC divider value high"]
pub type DivR = crate::FieldReader;
impl R {
    #[doc = "Bits 0:3 - RTC divider value high"]
    #[inline(always)]
    pub fn div(&self) -> DivR {
        DivR::new((self.bits & 0x0f) as u8)
    }
}
#[doc = "RTC divider high register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`divh::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DivhSpec;
impl crate::RegisterSpec for DivhSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`divh::R`](R) reader structure"]
impl crate::Readable for DivhSpec {}
#[doc = "`reset()` method sets DIVH to value 0"]
impl crate::Resettable for DivhSpec {
    const RESET_VALUE: u32 = 0;
}
