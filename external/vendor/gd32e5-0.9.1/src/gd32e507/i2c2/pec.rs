#[doc = "Register `PEC` reader"]
pub type R = crate::R<PecSpec>;
#[doc = "Field `PECV` reader - Packet Error Checking Value"]
pub type PecvR = crate::FieldReader;
impl R {
    #[doc = "Bits 0:7 - Packet Error Checking Value"]
    #[inline(always)]
    pub fn pecv(&self) -> PecvR {
        PecvR::new((self.bits & 0xff) as u8)
    }
}
#[doc = "Packet Error Checking\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pec::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PecSpec;
impl crate::RegisterSpec for PecSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pec::R`](R) reader structure"]
impl crate::Readable for PecSpec {}
#[doc = "`reset()` method sets PEC to value 0"]
impl crate::Resettable for PecSpec {
    const RESET_VALUE: u32 = 0;
}
