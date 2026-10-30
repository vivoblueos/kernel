#[doc = "Register `HP_LP_CPU_COMM` writer"]
pub type W = crate::W<HP_LP_CPU_COMM_SPEC>;
#[doc = "Field `LP_TRIGGER_HP` writer - need_des"]
pub type LP_TRIGGER_HP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_TRIGGER_LP` writer - need_des"]
pub type HP_TRIGGER_LP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<HP_LP_CPU_COMM_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn lp_trigger_hp(&mut self) -> LP_TRIGGER_HP_W<'_, HP_LP_CPU_COMM_SPEC> {
        LP_TRIGGER_HP_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn hp_trigger_lp(&mut self) -> HP_TRIGGER_LP_W<'_, HP_LP_CPU_COMM_SPEC> {
        HP_TRIGGER_LP_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hp_lp_cpu_comm::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_LP_CPU_COMM_SPEC;
impl crate::RegisterSpec for HP_LP_CPU_COMM_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`hp_lp_cpu_comm::W`](W) writer structure"]
impl crate::Writable for HP_LP_CPU_COMM_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HP_LP_CPU_COMM to value 0"]
impl crate::Resettable for HP_LP_CPU_COMM_SPEC {}
