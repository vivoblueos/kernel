#[doc = "Register `SLC1_HOST_PF` reader"]
pub type R = crate::R<SLC1_HOST_PF_SPEC>;
#[doc = "Field `SLC1_PF_DATA` reader - *******Description***********"]
pub type SLC1_PF_DATA_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - *******Description***********"]
    #[inline(always)]
    pub fn slc1_pf_data(&self) -> SLC1_PF_DATA_R {
        SLC1_PF_DATA_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC1_HOST_PF")
            .field("slc1_pf_data", &self.slc1_pf_data())
            .finish()
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1_host_pf::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC1_HOST_PF_SPEC;
impl crate::RegisterSpec for SLC1_HOST_PF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc1_host_pf::R`](R) reader structure"]
impl crate::Readable for SLC1_HOST_PF_SPEC {}
#[doc = "`reset()` method sets SLC1_HOST_PF to value 0"]
impl crate::Resettable for SLC1_HOST_PF_SPEC {}
