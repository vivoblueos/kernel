#[doc = "Register `TIME_LOW0` reader"]
pub type R = crate::R<TIME_LOW0_SPEC>;
#[doc = "Field `TIMER_VALUE0_LOW` reader - RTC timer low 32 bits"]
pub type TIMER_VALUE0_LOW_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - RTC timer low 32 bits"]
    #[inline(always)]
    pub fn timer_value0_low(&self) -> TIMER_VALUE0_LOW_R {
        TIMER_VALUE0_LOW_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TIME_LOW0")
            .field("timer_value0_low", &self.timer_value0_low())
            .finish()
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`time_low0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TIME_LOW0_SPEC;
impl crate::RegisterSpec for TIME_LOW0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`time_low0::R`](R) reader structure"]
impl crate::Readable for TIME_LOW0_SPEC {}
#[doc = "`reset()` method sets TIME_LOW0 to value 0"]
impl crate::Resettable for TIME_LOW0_SPEC {}
