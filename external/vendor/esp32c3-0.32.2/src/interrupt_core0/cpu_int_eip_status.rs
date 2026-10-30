#[doc = "Register `CPU_INT_EIP_STATUS` reader"]
pub type R = crate::R<CPU_INT_EIP_STATUS_SPEC>;
#[doc = "Field `CPU_INT_EIP_STATUS` reader - reg_core0_cpu_int_eip_status"]
pub type CPU_INT_EIP_STATUS_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - reg_core0_cpu_int_eip_status"]
    #[inline(always)]
    pub fn cpu_int_eip_status(&self) -> CPU_INT_EIP_STATUS_R {
        CPU_INT_EIP_STATUS_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CPU_INT_EIP_STATUS")
            .field("cpu_int_eip_status", &self.cpu_int_eip_status())
            .finish()
    }
}
#[doc = "mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_int_eip_status::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CPU_INT_EIP_STATUS_SPEC;
impl crate::RegisterSpec for CPU_INT_EIP_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cpu_int_eip_status::R`](R) reader structure"]
impl crate::Readable for CPU_INT_EIP_STATUS_SPEC {}
#[doc = "`reset()` method sets CPU_INT_EIP_STATUS to value 0"]
impl crate::Resettable for CPU_INT_EIP_STATUS_SPEC {}
