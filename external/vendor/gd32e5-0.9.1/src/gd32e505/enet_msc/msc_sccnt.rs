#[doc = "Register `MSC_SCCNT` reader"]
pub type R = crate::R<MscSccntSpec>;
#[doc = "Field `SCC` reader - Transmitted good frames after a single collision counter"]
pub type SccR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Transmitted good frames after a single collision counter"]
    #[inline(always)]
    pub fn scc(&self) -> SccR {
        SccR::new(self.bits)
    }
}
#[doc = "Ethernet MSC transmitted good frames after a single collision counter\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_sccnt::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MscSccntSpec;
impl crate::RegisterSpec for MscSccntSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`msc_sccnt::R`](R) reader structure"]
impl crate::Readable for MscSccntSpec {}
#[doc = "`reset()` method sets MSC_SCCNT to value 0"]
impl crate::Resettable for MscSccntSpec {
    const RESET_VALUE: u32 = 0;
}
