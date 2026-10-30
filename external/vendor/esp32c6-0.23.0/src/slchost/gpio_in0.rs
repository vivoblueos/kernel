#[doc = "Register `GPIO_IN0` reader"]
pub type R = crate::R<GPIO_IN0_SPEC>;
#[doc = "Field `GPIO_SDIO_IN0` reader - *******Description***********"]
pub type GPIO_SDIO_IN0_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - *******Description***********"]
    #[inline(always)]
    pub fn gpio_sdio_in0(&self) -> GPIO_SDIO_IN0_R {
        GPIO_SDIO_IN0_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("GPIO_IN0")
            .field("gpio_sdio_in0", &self.gpio_sdio_in0())
            .finish()
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`gpio_in0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GPIO_IN0_SPEC;
impl crate::RegisterSpec for GPIO_IN0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`gpio_in0::R`](R) reader structure"]
impl crate::Readable for GPIO_IN0_SPEC {}
#[doc = "`reset()` method sets GPIO_IN0 to value 0"]
impl crate::Resettable for GPIO_IN0_SPEC {}
