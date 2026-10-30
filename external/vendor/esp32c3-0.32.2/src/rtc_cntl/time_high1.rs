#[doc = "Register `TIME_HIGH1` reader"]
pub type R = crate::R<TIME_HIGH1_SPEC>;
#[doc = "Field `TIMER_VALUE1_HIGH` reader - RTC timer high 16 bits"]
pub type TIMER_VALUE1_HIGH_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - RTC timer high 16 bits"]
    #[inline(always)]
    pub fn timer_value1_high(&self) -> TIMER_VALUE1_HIGH_R {
        TIMER_VALUE1_HIGH_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TIME_HIGH1")
            .field("timer_value1_high", &self.timer_value1_high())
            .finish()
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`time_high1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TIME_HIGH1_SPEC;
impl crate::RegisterSpec for TIME_HIGH1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`time_high1::R`](R) reader structure"]
impl crate::Readable for TIME_HIGH1_SPEC {}
#[doc = "`reset()` method sets TIME_HIGH1 to value 0"]
impl crate::Resettable for TIME_HIGH1_SPEC {}
