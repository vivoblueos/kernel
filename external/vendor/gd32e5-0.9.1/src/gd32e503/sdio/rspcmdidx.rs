#[doc = "Register `RSPCMDIDX` reader"]
pub type R = crate::R<RspcmdidxSpec>;
#[doc = "Field `RSPCMDIDX` reader - Last response command index"]
pub type RspcmdidxR = crate::FieldReader;
impl R {
    #[doc = "Bits 0:5 - Last response command index"]
    #[inline(always)]
    pub fn rspcmdidx(&self) -> RspcmdidxR {
        RspcmdidxR::new((self.bits & 0x3f) as u8)
    }
}
#[doc = "Command index response register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rspcmdidx::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RspcmdidxSpec;
impl crate::RegisterSpec for RspcmdidxSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rspcmdidx::R`](R) reader structure"]
impl crate::Readable for RspcmdidxSpec {}
#[doc = "`reset()` method sets RSPCMDIDX to value 0"]
impl crate::Resettable for RspcmdidxSpec {
    const RESET_VALUE: u32 = 0;
}
