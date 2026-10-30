#[doc = "Register `MSC_TGFCNT` reader"]
pub type R = crate::R<MscTgfcntSpec>;
#[doc = "Field `TGF` reader - Transmitted good frames counter"]
pub type TgfR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Transmitted good frames counter"]
    #[inline(always)]
    pub fn tgf(&self) -> TgfR {
        TgfR::new(self.bits)
    }
}
#[doc = "Ethernet MSC transmitted good frames counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_tgfcnt::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MscTgfcntSpec;
impl crate::RegisterSpec for MscTgfcntSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`msc_tgfcnt::R`](R) reader structure"]
impl crate::Readable for MscTgfcntSpec {}
#[doc = "`reset()` method sets MSC_TGFCNT to value 0"]
impl crate::Resettable for MscTgfcntSpec {
    const RESET_VALUE: u32 = 0;
}
