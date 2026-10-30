#[doc = "Register `SLC0_HOST_PF` reader"]
pub type R = crate::R<SLC0_HOST_PF_SPEC>;
#[doc = "Field `SLC0_PF_DATA` reader - *******Description***********"]
pub type SLC0_PF_DATA_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_pf_data(&self) -> SLC0_PF_DATA_R {
        SLC0_PF_DATA_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC0_HOST_PF")
            .field("slc0_pf_data", &self.slc0_pf_data())
            .finish()
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0_host_pf::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC0_HOST_PF_SPEC;
impl crate::RegisterSpec for SLC0_HOST_PF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc0_host_pf::R`](R) reader structure"]
impl crate::Readable for SLC0_HOST_PF_SPEC {}
#[doc = "`reset()` method sets SLC0_HOST_PF to value 0"]
impl crate::Resettable for SLC0_HOST_PF_SPEC {}
