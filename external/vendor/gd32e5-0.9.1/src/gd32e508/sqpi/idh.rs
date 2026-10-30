#[doc = "Register `IDH` reader"]
pub type R = crate::R<IdhSpec>;
#[doc = "Field `SQPI_IDH` reader - ID High Data saved for SQPI read ID command"]
pub type SqpiIdhR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - ID High Data saved for SQPI read ID command"]
    #[inline(always)]
    pub fn sqpi_idh(&self) -> SqpiIdhR {
        SqpiIdhR::new(self.bits)
    }
}
#[doc = "ID High Register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`idh::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IdhSpec;
impl crate::RegisterSpec for IdhSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`idh::R`](R) reader structure"]
impl crate::Readable for IdhSpec {}
#[doc = "`reset()` method sets IDH to value 0"]
impl crate::Resettable for IdhSpec {
    const RESET_VALUE: u32 = 0;
}
