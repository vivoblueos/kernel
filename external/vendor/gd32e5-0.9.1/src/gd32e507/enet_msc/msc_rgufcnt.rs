#[doc = "Register `MSC_RGUFCNT` reader"]
pub type R = crate::R<MscRgufcntSpec>;
#[doc = "Field `RGUF` reader - Received good unicast frames counter"]
pub type RgufR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Received good unicast frames counter"]
    #[inline(always)]
    pub fn rguf(&self) -> RgufR {
        RgufR::new(self.bits)
    }
}
#[doc = "MSC received good unicast frames counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_rgufcnt::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MscRgufcntSpec;
impl crate::RegisterSpec for MscRgufcntSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`msc_rgufcnt::R`](R) reader structure"]
impl crate::Readable for MscRgufcntSpec {}
#[doc = "`reset()` method sets MSC_RGUFCNT to value 0"]
impl crate::Resettable for MscRgufcntSpec {
    const RESET_VALUE: u32 = 0;
}
