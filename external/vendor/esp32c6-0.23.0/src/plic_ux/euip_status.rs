#[doc = "Register `EUIP_STATUS` reader"]
pub type R = crate::R<EUIP_STATUS_SPEC>;
#[doc = "Field `CPU_EIP_STATUS` reader - "]
pub type CPU_EIP_STATUS_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn cpu_eip_status(&self) -> CPU_EIP_STATUS_R {
        CPU_EIP_STATUS_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("EUIP_STATUS")
            .field("cpu_eip_status", &self.cpu_eip_status())
            .finish()
    }
}
#[doc = "PLIC EMIP Status Register\n\nYou can [`read`](crate::Reg::read) this register and get [`euip_status::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct EUIP_STATUS_SPEC;
impl crate::RegisterSpec for EUIP_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`euip_status::R`](R) reader structure"]
impl crate::Readable for EUIP_STATUS_SPEC {}
#[doc = "`reset()` method sets EUIP_STATUS to value 0"]
impl crate::Resettable for EUIP_STATUS_SPEC {}
