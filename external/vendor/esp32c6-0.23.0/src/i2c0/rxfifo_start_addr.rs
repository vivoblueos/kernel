#[doc = "Register `RXFIFO_START_ADDR` reader"]
pub type R = crate::R<RXFIFO_START_ADDR_SPEC>;
#[doc = "Field `RXFIFO_START_ADDR` reader - This is the I2C rxfifo first address."]
pub type RXFIFO_START_ADDR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - This is the I2C rxfifo first address."]
    #[inline(always)]
    pub fn rxfifo_start_addr(&self) -> RXFIFO_START_ADDR_R {
        RXFIFO_START_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RXFIFO_START_ADDR")
            .field("rxfifo_start_addr", &self.rxfifo_start_addr())
            .finish()
    }
}
#[doc = "I2C RXFIFO base address register\n\nYou can [`read`](crate::Reg::read) this register and get [`rxfifo_start_addr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RXFIFO_START_ADDR_SPEC;
impl crate::RegisterSpec for RXFIFO_START_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rxfifo_start_addr::R`](R) reader structure"]
impl crate::Readable for RXFIFO_START_ADDR_SPEC {}
#[doc = "`reset()` method sets RXFIFO_START_ADDR to value 0"]
impl crate::Resettable for RXFIFO_START_ADDR_SPEC {}
