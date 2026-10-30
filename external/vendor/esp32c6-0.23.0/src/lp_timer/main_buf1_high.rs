#[doc = "Register `MAIN_BUF1_HIGH` reader"]
pub type R = crate::R<MAIN_BUF1_HIGH_SPEC>;
#[doc = "Field `MAIN_TIMER_BUF1_HIGH` reader - need_des"]
pub type MAIN_TIMER_BUF1_HIGH_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - need_des"]
    #[inline(always)]
    pub fn main_timer_buf1_high(&self) -> MAIN_TIMER_BUF1_HIGH_R {
        MAIN_TIMER_BUF1_HIGH_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MAIN_BUF1_HIGH")
            .field("main_timer_buf1_high", &self.main_timer_buf1_high())
            .finish()
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`main_buf1_high::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MAIN_BUF1_HIGH_SPEC;
impl crate::RegisterSpec for MAIN_BUF1_HIGH_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`main_buf1_high::R`](R) reader structure"]
impl crate::Readable for MAIN_BUF1_HIGH_SPEC {}
#[doc = "`reset()` method sets MAIN_BUF1_HIGH to value 0"]
impl crate::Resettable for MAIN_BUF1_HIGH_SPEC {}
