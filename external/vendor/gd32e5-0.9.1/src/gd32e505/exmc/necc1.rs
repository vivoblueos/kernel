#[doc = "Register `NECC1` reader"]
pub type R = crate::R<Necc1Spec>;
#[doc = "Field `ECC` reader - ECC result"]
pub type EccR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - ECC result"]
    #[inline(always)]
    pub fn ecc(&self) -> EccR {
        EccR::new(self.bits)
    }
}
#[doc = "NAND flash ECC register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`necc1::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Necc1Spec;
impl crate::RegisterSpec for Necc1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`necc1::R`](R) reader structure"]
impl crate::Readable for Necc1Spec {}
#[doc = "`reset()` method sets NECC1 to value 0"]
impl crate::Resettable for Necc1Spec {
    const RESET_VALUE: u32 = 0;
}
