#[doc = "Register `IDATA0` reader"]
pub type R = crate::R<Idata0Spec>;
#[doc = "Field `IDATAn` reader - Inserted number n conversion data"]
pub type IdatanR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - Inserted number n conversion data"]
    #[inline(always)]
    pub fn idatan(&self) -> IdatanR {
        IdatanR::new((self.bits & 0xffff) as u16)
    }
}
#[doc = "Inserted data register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`idata0::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Idata0Spec;
impl crate::RegisterSpec for Idata0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`idata0::R`](R) reader structure"]
impl crate::Readable for Idata0Spec {}
#[doc = "`reset()` method sets IDATA0 to value 0"]
impl crate::Resettable for Idata0Spec {
    const RESET_VALUE: u32 = 0;
}
