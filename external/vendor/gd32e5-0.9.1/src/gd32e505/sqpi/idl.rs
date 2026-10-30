#[doc = "Register `IDL` reader"]
pub type R = crate::R<IdlSpec>;
#[doc = "Field `SQPI_IDL` reader - ID Low Data saved for SQPI Read ID Command"]
pub type SqpiIdlR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - ID Low Data saved for SQPI Read ID Command"]
    #[inline(always)]
    pub fn sqpi_idl(&self) -> SqpiIdlR {
        SqpiIdlR::new(self.bits)
    }
}
#[doc = "ID Low Register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`idl::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IdlSpec;
impl crate::RegisterSpec for IdlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`idl::R`](R) reader structure"]
impl crate::Readable for IdlSpec {}
#[doc = "`reset()` method sets IDL to value 0"]
impl crate::Resettable for IdlSpec {
    const RESET_VALUE: u32 = 0;
}
