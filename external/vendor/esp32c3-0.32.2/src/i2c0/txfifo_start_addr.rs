#[doc = "Register `TXFIFO_START_ADDR` reader"]
pub type R = crate::R<TXFIFO_START_ADDR_SPEC>;
#[doc = "Field `TXFIFO_START_ADDR` reader - reg_txfifo_start_addr."]
pub type TXFIFO_START_ADDR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - reg_txfifo_start_addr."]
    #[inline(always)]
    pub fn txfifo_start_addr(&self) -> TXFIFO_START_ADDR_R {
        TXFIFO_START_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TXFIFO_START_ADDR")
            .field("txfifo_start_addr", &self.txfifo_start_addr())
            .finish()
    }
}
#[doc = "I2C_TXFIFO_START_ADDR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`txfifo_start_addr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TXFIFO_START_ADDR_SPEC;
impl crate::RegisterSpec for TXFIFO_START_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`txfifo_start_addr::R`](R) reader structure"]
impl crate::Readable for TXFIFO_START_ADDR_SPEC {}
#[doc = "`reset()` method sets TXFIFO_START_ADDR to value 0"]
impl crate::Resettable for TXFIFO_START_ADDR_SPEC {}
