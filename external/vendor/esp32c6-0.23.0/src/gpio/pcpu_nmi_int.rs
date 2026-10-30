#[doc = "Register `PCPU_NMI_INT` reader"]
pub type R = crate::R<PCPU_NMI_INT_SPEC>;
#[doc = "Field `PROCPU_NMI_INT` reader - GPIO PRO_CPU(not shielded) interrupt status register for GPIO0-31"]
pub type PROCPU_NMI_INT_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - GPIO PRO_CPU(not shielded) interrupt status register for GPIO0-31"]
    #[inline(always)]
    pub fn procpu_nmi_int(&self) -> PROCPU_NMI_INT_R {
        PROCPU_NMI_INT_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PCPU_NMI_INT")
            .field("procpu_nmi_int", &self.procpu_nmi_int())
            .finish()
    }
}
#[doc = "GPIO PRO_CPU(not shielded) interrupt status register for GPIO0-31\n\nYou can [`read`](crate::Reg::read) this register and get [`pcpu_nmi_int::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PCPU_NMI_INT_SPEC;
impl crate::RegisterSpec for PCPU_NMI_INT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pcpu_nmi_int::R`](R) reader structure"]
impl crate::Readable for PCPU_NMI_INT_SPEC {}
#[doc = "`reset()` method sets PCPU_NMI_INT to value 0"]
impl crate::Resettable for PCPU_NMI_INT_SPEC {}
