#[doc = "Register `INTERRUPT_SOURCE` reader"]
pub type R = crate::R<INTERRUPT_SOURCE_SPEC>;
#[doc = "Field `LP_INTERRUPT_SOURCE` reader - BIT5~BIT0: pmu_lp_int, modem_lp_int, lp_timer_lp_int, lp_uart_int, lp_i2c_int, lp_io_int"]
pub type LP_INTERRUPT_SOURCE_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:5 - BIT5~BIT0: pmu_lp_int, modem_lp_int, lp_timer_lp_int, lp_uart_int, lp_i2c_int, lp_io_int"]
    #[inline(always)]
    pub fn lp_interrupt_source(&self) -> LP_INTERRUPT_SOURCE_R {
        LP_INTERRUPT_SOURCE_R::new((self.bits & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INTERRUPT_SOURCE")
            .field("lp_interrupt_source", &self.lp_interrupt_source())
            .finish()
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`interrupt_source::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INTERRUPT_SOURCE_SPEC;
impl crate::RegisterSpec for INTERRUPT_SOURCE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`interrupt_source::R`](R) reader structure"]
impl crate::Readable for INTERRUPT_SOURCE_SPEC {}
#[doc = "`reset()` method sets INTERRUPT_SOURCE to value 0"]
impl crate::Resettable for INTERRUPT_SOURCE_SPEC {}
