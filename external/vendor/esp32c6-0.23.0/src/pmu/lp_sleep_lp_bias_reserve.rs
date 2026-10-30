#[doc = "Register `LP_SLEEP_LP_BIAS_RESERVE` writer"]
pub type W = crate::W<LP_SLEEP_LP_BIAS_RESERVE_SPEC>;
#[doc = "Field `LP_SLEEP_LP_BIAS_RESERVE` writer - need_des"]
pub type LP_SLEEP_LP_BIAS_RESERVE_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<LP_SLEEP_LP_BIAS_RESERVE_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn lp_sleep_lp_bias_reserve(
        &mut self,
    ) -> LP_SLEEP_LP_BIAS_RESERVE_W<'_, LP_SLEEP_LP_BIAS_RESERVE_SPEC> {
        LP_SLEEP_LP_BIAS_RESERVE_W::new(self, 0)
    }
}
#[doc = "need_des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lp_sleep_lp_bias_reserve::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LP_SLEEP_LP_BIAS_RESERVE_SPEC;
impl crate::RegisterSpec for LP_SLEEP_LP_BIAS_RESERVE_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`lp_sleep_lp_bias_reserve::W`](W) writer structure"]
impl crate::Writable for LP_SLEEP_LP_BIAS_RESERVE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LP_SLEEP_LP_BIAS_RESERVE to value 0"]
impl crate::Resettable for LP_SLEEP_LP_BIAS_RESERVE_SPEC {}
