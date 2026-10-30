#[doc = "Register `TIMER%s_CNT_CAP` reader"]
pub type R = crate::R<TIMER_CNT_CAP_SPEC>;
#[doc = "Field `TIMER_CNT_CAP` reader - This register stores ledc timer%s count value."]
pub type TIMER_CNT_CAP_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:19 - This register stores ledc timer%s count value."]
    #[inline(always)]
    pub fn timer_cnt_cap(&self) -> TIMER_CNT_CAP_R {
        TIMER_CNT_CAP_R::new(self.bits & 0x000f_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TIMER_CNT_CAP")
            .field("timer_cnt_cap", &self.timer_cnt_cap())
            .finish()
    }
}
#[doc = "Ledc timer%s count value capture register.\n\nYou can [`read`](crate::Reg::read) this register and get [`timer_cnt_cap::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TIMER_CNT_CAP_SPEC;
impl crate::RegisterSpec for TIMER_CNT_CAP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`timer_cnt_cap::R`](R) reader structure"]
impl crate::Readable for TIMER_CNT_CAP_SPEC {}
#[doc = "`reset()` method sets TIMER%s_CNT_CAP to value 0"]
impl crate::Resettable for TIMER_CNT_CAP_SPEC {}
