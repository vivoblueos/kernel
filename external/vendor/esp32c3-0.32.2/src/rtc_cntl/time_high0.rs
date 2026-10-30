#[doc = "Register `TIME_HIGH0` reader"]
pub type R = crate::R<TIME_HIGH0_SPEC>;
#[doc = "Field `TIMER_VALUE0_HIGH` reader - RTC timer high 16 bits"]
pub type TIMER_VALUE0_HIGH_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - RTC timer high 16 bits"]
    #[inline(always)]
    pub fn timer_value0_high(&self) -> TIMER_VALUE0_HIGH_R {
        TIMER_VALUE0_HIGH_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TIME_HIGH0")
            .field("timer_value0_high", &self.timer_value0_high())
            .finish()
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`time_high0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TIME_HIGH0_SPEC;
impl crate::RegisterSpec for TIME_HIGH0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`time_high0::R`](R) reader structure"]
impl crate::Readable for TIME_HIGH0_SPEC {}
#[doc = "`reset()` method sets TIME_HIGH0 to value 0"]
impl crate::Resettable for TIME_HIGH0_SPEC {}
