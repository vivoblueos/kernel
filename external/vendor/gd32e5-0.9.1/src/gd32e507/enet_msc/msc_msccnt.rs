#[doc = "Register `MSC_MSCCNT` reader"]
pub type R = crate::R<MscMsccntSpec>;
#[doc = "Field `MSCC` reader - Transmitted good frames after more than a single collision counter"]
pub type MsccR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Transmitted good frames after more than a single collision counter"]
    #[inline(always)]
    pub fn mscc(&self) -> MsccR {
        MsccR::new(self.bits)
    }
}
#[doc = "Ethernet MSC transmitted good frames after more than a single collision\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_msccnt::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MscMsccntSpec;
impl crate::RegisterSpec for MscMsccntSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`msc_msccnt::R`](R) reader structure"]
impl crate::Readable for MscMsccntSpec {}
#[doc = "`reset()` method sets MSC_MSCCNT to value 0"]
impl crate::Resettable for MscMsccntSpec {
    const RESET_VALUE: u32 = 0;
}
