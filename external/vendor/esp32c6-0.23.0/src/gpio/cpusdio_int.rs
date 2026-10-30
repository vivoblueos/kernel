#[doc = "Register `CPUSDIO_INT` reader"]
pub type R = crate::R<CPUSDIO_INT_SPEC>;
#[doc = "Field `SDIO_INT` reader - GPIO CPUSDIO interrupt status register for GPIO0-31"]
pub type SDIO_INT_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - GPIO CPUSDIO interrupt status register for GPIO0-31"]
    #[inline(always)]
    pub fn sdio_int(&self) -> SDIO_INT_R {
        SDIO_INT_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CPUSDIO_INT")
            .field("sdio_int", &self.sdio_int())
            .finish()
    }
}
#[doc = "GPIO CPUSDIO interrupt status register for GPIO0-31\n\nYou can [`read`](crate::Reg::read) this register and get [`cpusdio_int::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CPUSDIO_INT_SPEC;
impl crate::RegisterSpec for CPUSDIO_INT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cpusdio_int::R`](R) reader structure"]
impl crate::Readable for CPUSDIO_INT_SPEC {}
#[doc = "`reset()` method sets CPUSDIO_INT to value 0"]
impl crate::Resettable for CPUSDIO_INT_SPEC {}
