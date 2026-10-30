#[doc = "Register `NECC2` reader"]
pub type R = crate::R<Necc2Spec>;
#[doc = "Field `ECC` reader - ECC result"]
pub type EccR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - ECC result"]
    #[inline(always)]
    pub fn ecc(&self) -> EccR {
        EccR::new(self.bits)
    }
}
#[doc = "NAND flash ECC register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`necc2::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Necc2Spec;
impl crate::RegisterSpec for Necc2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`necc2::R`](R) reader structure"]
impl crate::Readable for Necc2Spec {}
#[doc = "`reset()` method sets NECC2 to value 0"]
impl crate::Resettable for Necc2Spec {
    const RESET_VALUE: u32 = 0;
}
