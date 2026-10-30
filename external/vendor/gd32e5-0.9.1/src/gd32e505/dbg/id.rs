#[doc = "Register `ID` reader"]
pub type R = crate::R<IdSpec>;
#[doc = "Field `ID_CODE` reader - DBG ID code register"]
pub type IdCodeR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - DBG ID code register"]
    #[inline(always)]
    pub fn id_code(&self) -> IdCodeR {
        IdCodeR::new(self.bits)
    }
}
#[doc = "ID code register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`id::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IdSpec;
impl crate::RegisterSpec for IdSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`id::R`](R) reader structure"]
impl crate::Readable for IdSpec {}
#[doc = "`reset()` method sets ID to value 0"]
impl crate::Resettable for IdSpec {
    const RESET_VALUE: u32 = 0;
}
