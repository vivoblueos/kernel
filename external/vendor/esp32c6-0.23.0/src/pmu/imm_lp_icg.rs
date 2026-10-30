#[doc = "Register `IMM_LP_ICG` writer"]
pub type W = crate::W<IMM_LP_ICG_SPEC>;
#[doc = "Field `TIE_LOW_LP_ROOTCLK_SEL` writer - need_des"]
pub type TIE_LOW_LP_ROOTCLK_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_HIGH_LP_ROOTCLK_SEL` writer - need_des"]
pub type TIE_HIGH_LP_ROOTCLK_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<IMM_LP_ICG_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn tie_low_lp_rootclk_sel(&mut self) -> TIE_LOW_LP_ROOTCLK_SEL_W<'_, IMM_LP_ICG_SPEC> {
        TIE_LOW_LP_ROOTCLK_SEL_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn tie_high_lp_rootclk_sel(&mut self) -> TIE_HIGH_LP_ROOTCLK_SEL_W<'_, IMM_LP_ICG_SPEC> {
        TIE_HIGH_LP_ROOTCLK_SEL_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`imm_lp_icg::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IMM_LP_ICG_SPEC;
impl crate::RegisterSpec for IMM_LP_ICG_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`imm_lp_icg::W`](W) writer structure"]
impl crate::Writable for IMM_LP_ICG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IMM_LP_ICG to value 0"]
impl crate::Resettable for IMM_LP_ICG_SPEC {}
