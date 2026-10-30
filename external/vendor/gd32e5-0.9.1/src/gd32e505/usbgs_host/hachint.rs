#[doc = "Register `HACHINT` reader"]
pub type R = crate::R<HachintSpec>;
#[doc = "Field `HACHINT` reader - Host all channel interrupts"]
pub type HachintR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:11 - Host all channel interrupts"]
    #[inline(always)]
    pub fn hachint(&self) -> HachintR {
        HachintR::new((self.bits & 0x0fff) as u16)
    }
}
#[doc = "Host all channels interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hachint::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HachintSpec;
impl crate::RegisterSpec for HachintSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hachint::R`](R) reader structure"]
impl crate::Readable for HachintSpec {}
#[doc = "`reset()` method sets HACHINT to value 0"]
impl crate::Resettable for HachintSpec {
    const RESET_VALUE: u32 = 0;
}
