#[doc = "Register `IDATA3` reader"]
pub type R = crate::R<Idata3Spec>;
#[doc = "Field `IDATAn` reader - Inserted number n conversion data"]
pub type IdatanR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - Inserted number n conversion data"]
    #[inline(always)]
    pub fn idatan(&self) -> IdatanR {
        IdatanR::new((self.bits & 0xffff) as u16)
    }
}
#[doc = "Inserted data register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`idata3::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Idata3Spec;
impl crate::RegisterSpec for Idata3Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`idata3::R`](R) reader structure"]
impl crate::Readable for Idata3Spec {}
#[doc = "`reset()` method sets IDATA3 to value 0"]
impl crate::Resettable for Idata3Spec {
    const RESET_VALUE: u32 = 0;
}
