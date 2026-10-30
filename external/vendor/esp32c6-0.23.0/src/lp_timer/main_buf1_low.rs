#[doc = "Register `MAIN_BUF1_LOW` reader"]
pub type R = crate::R<MAIN_BUF1_LOW_SPEC>;
#[doc = "Field `MAIN_TIMER_BUF1_LOW` reader - need_des"]
pub type MAIN_TIMER_BUF1_LOW_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn main_timer_buf1_low(&self) -> MAIN_TIMER_BUF1_LOW_R {
        MAIN_TIMER_BUF1_LOW_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MAIN_BUF1_LOW")
            .field("main_timer_buf1_low", &self.main_timer_buf1_low())
            .finish()
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`main_buf1_low::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MAIN_BUF1_LOW_SPEC;
impl crate::RegisterSpec for MAIN_BUF1_LOW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`main_buf1_low::R`](R) reader structure"]
impl crate::Readable for MAIN_BUF1_LOW_SPEC {}
#[doc = "`reset()` method sets MAIN_BUF1_LOW to value 0"]
impl crate::Resettable for MAIN_BUF1_LOW_SPEC {}
