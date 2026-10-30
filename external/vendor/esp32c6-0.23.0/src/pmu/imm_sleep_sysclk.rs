#[doc = "Register `IMM_SLEEP_SYSCLK` writer"]
pub type W = crate::W<IMM_SLEEP_SYSCLK_SPEC>;
#[doc = "Field `UPDATE_DIG_ICG_SWITCH` writer - need_des"]
pub type UPDATE_DIG_ICG_SWITCH_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_LOW_ICG_SLP_SEL` writer - need_des"]
pub type TIE_LOW_ICG_SLP_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_HIGH_ICG_SLP_SEL` writer - need_des"]
pub type TIE_HIGH_ICG_SLP_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UPDATE_DIG_SYS_CLK_SEL` writer - need_des"]
pub type UPDATE_DIG_SYS_CLK_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<IMM_SLEEP_SYSCLK_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn update_dig_icg_switch(&mut self) -> UPDATE_DIG_ICG_SWITCH_W<'_, IMM_SLEEP_SYSCLK_SPEC> {
        UPDATE_DIG_ICG_SWITCH_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn tie_low_icg_slp_sel(&mut self) -> TIE_LOW_ICG_SLP_SEL_W<'_, IMM_SLEEP_SYSCLK_SPEC> {
        TIE_LOW_ICG_SLP_SEL_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn tie_high_icg_slp_sel(&mut self) -> TIE_HIGH_ICG_SLP_SEL_W<'_, IMM_SLEEP_SYSCLK_SPEC> {
        TIE_HIGH_ICG_SLP_SEL_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn update_dig_sys_clk_sel(
        &mut self,
    ) -> UPDATE_DIG_SYS_CLK_SEL_W<'_, IMM_SLEEP_SYSCLK_SPEC> {
        UPDATE_DIG_SYS_CLK_SEL_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`imm_sleep_sysclk::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IMM_SLEEP_SYSCLK_SPEC;
impl crate::RegisterSpec for IMM_SLEEP_SYSCLK_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`imm_sleep_sysclk::W`](W) writer structure"]
impl crate::Writable for IMM_SLEEP_SYSCLK_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IMM_SLEEP_SYSCLK to value 0"]
impl crate::Resettable for IMM_SLEEP_SYSCLK_SPEC {}
