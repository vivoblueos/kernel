#[doc = "Register `DAEPINT` reader"]
pub type R = crate::R<DaepintSpec>;
#[doc = "Field `IEPITB` reader - Device all IN endpoint interrupt bits"]
pub type IepitbR = crate::FieldReader;
#[doc = "Field `OEPITB` reader - Device all OUT endpoint interrupt bits"]
pub type OepitbR = crate::FieldReader;
impl R {
    #[doc = "Bits 0:5 - Device all IN endpoint interrupt bits"]
    #[inline(always)]
    pub fn iepitb(&self) -> IepitbR {
        IepitbR::new((self.bits & 0x3f) as u8)
    }
    #[doc = "Bits 16:21 - Device all OUT endpoint interrupt bits"]
    #[inline(always)]
    pub fn oepitb(&self) -> OepitbR {
        OepitbR::new(((self.bits >> 16) & 0x3f) as u8)
    }
}
#[doc = "device all endpoints interrupt register (DAEPINT)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`daepint::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DaepintSpec;
impl crate::RegisterSpec for DaepintSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`daepint::R`](R) reader structure"]
impl crate::Readable for DaepintSpec {}
#[doc = "`reset()` method sets DAEPINT to value 0"]
impl crate::Resettable for DaepintSpec {
    const RESET_VALUE: u32 = 0;
}
