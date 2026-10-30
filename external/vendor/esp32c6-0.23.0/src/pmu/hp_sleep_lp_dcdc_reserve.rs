#[doc = "Register `HP_SLEEP_LP_DCDC_RESERVE` writer"]
pub type W = crate::W<HP_SLEEP_LP_DCDC_RESERVE_SPEC>;
#[doc = "Field `HP_SLEEP_LP_DCDC_RESERVE` writer - need_des"]
pub type HP_SLEEP_LP_DCDC_RESERVE_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<HP_SLEEP_LP_DCDC_RESERVE_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_lp_dcdc_reserve(
        &mut self,
    ) -> HP_SLEEP_LP_DCDC_RESERVE_W<'_, HP_SLEEP_LP_DCDC_RESERVE_SPEC> {
        HP_SLEEP_LP_DCDC_RESERVE_W::new(self, 0)
    }
}
#[doc = "need_des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hp_sleep_lp_dcdc_reserve::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_SLEEP_LP_DCDC_RESERVE_SPEC;
impl crate::RegisterSpec for HP_SLEEP_LP_DCDC_RESERVE_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`hp_sleep_lp_dcdc_reserve::W`](W) writer structure"]
impl crate::Writable for HP_SLEEP_LP_DCDC_RESERVE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HP_SLEEP_LP_DCDC_RESERVE to value 0"]
impl crate::Resettable for HP_SLEEP_LP_DCDC_RESERVE_SPEC {}
