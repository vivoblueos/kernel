#[doc = "Register `HFINFR` reader"]
pub type R = crate::R<HfinfrSpec>;
#[doc = "Field `FRNUM` reader - Frame number"]
pub type FrnumR = crate::FieldReader<u16>;
#[doc = "Field `FRT` reader - Frame remaining time"]
pub type FrtR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - Frame number"]
    #[inline(always)]
    pub fn frnum(&self) -> FrnumR {
        FrnumR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:31 - Frame remaining time"]
    #[inline(always)]
    pub fn frt(&self) -> FrtR {
        FrtR::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
#[doc = "OTG_FS host frame number/frame time remaining register (HFINFR)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hfinfr::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HfinfrSpec;
impl crate::RegisterSpec for HfinfrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hfinfr::R`](R) reader structure"]
impl crate::Readable for HfinfrSpec {}
#[doc = "`reset()` method sets HFINFR to value 0xbb80_0000"]
impl crate::Resettable for HfinfrSpec {
    const RESET_VALUE: u32 = 0xbb80_0000;
}
