#[doc = "Register `PCPU_INT1` reader"]
pub type R = crate::R<PCPU_INT1_SPEC>;
#[doc = "Field `PROCPU_INT1` reader - GPIO PRO_CPU interrupt status register for GPIO32-34"]
pub type PROCPU_INT1_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:2 - GPIO PRO_CPU interrupt status register for GPIO32-34"]
    #[inline(always)]
    pub fn procpu_int1(&self) -> PROCPU_INT1_R {
        PROCPU_INT1_R::new((self.bits & 7) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PCPU_INT1")
            .field("procpu_int1", &self.procpu_int1())
            .finish()
    }
}
#[doc = "GPIO PRO_CPU interrupt status register for GPIO32-34\n\nYou can [`read`](crate::Reg::read) this register and get [`pcpu_int1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PCPU_INT1_SPEC;
impl crate::RegisterSpec for PCPU_INT1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pcpu_int1::R`](R) reader structure"]
impl crate::Readable for PCPU_INT1_SPEC {}
#[doc = "`reset()` method sets PCPU_INT1 to value 0"]
impl crate::Resettable for PCPU_INT1_SPEC {}
