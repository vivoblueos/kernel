#[doc = "Register `IMM_PAD_HOLD_ALL` writer"]
pub type W = crate::W<IMM_PAD_HOLD_ALL_SPEC>;
#[doc = "Field `TIE_HIGH_LP_PAD_HOLD_ALL` writer - need_des"]
pub type TIE_HIGH_LP_PAD_HOLD_ALL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_LOW_LP_PAD_HOLD_ALL` writer - need_des"]
pub type TIE_LOW_LP_PAD_HOLD_ALL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_HIGH_HP_PAD_HOLD_ALL` writer - need_des"]
pub type TIE_HIGH_HP_PAD_HOLD_ALL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_LOW_HP_PAD_HOLD_ALL` writer - need_des"]
pub type TIE_LOW_HP_PAD_HOLD_ALL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<IMM_PAD_HOLD_ALL_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn tie_high_lp_pad_hold_all(
        &mut self,
    ) -> TIE_HIGH_LP_PAD_HOLD_ALL_W<'_, IMM_PAD_HOLD_ALL_SPEC> {
        TIE_HIGH_LP_PAD_HOLD_ALL_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn tie_low_lp_pad_hold_all(
        &mut self,
    ) -> TIE_LOW_LP_PAD_HOLD_ALL_W<'_, IMM_PAD_HOLD_ALL_SPEC> {
        TIE_LOW_LP_PAD_HOLD_ALL_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn tie_high_hp_pad_hold_all(
        &mut self,
    ) -> TIE_HIGH_HP_PAD_HOLD_ALL_W<'_, IMM_PAD_HOLD_ALL_SPEC> {
        TIE_HIGH_HP_PAD_HOLD_ALL_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn tie_low_hp_pad_hold_all(
        &mut self,
    ) -> TIE_LOW_HP_PAD_HOLD_ALL_W<'_, IMM_PAD_HOLD_ALL_SPEC> {
        TIE_LOW_HP_PAD_HOLD_ALL_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`imm_pad_hold_all::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IMM_PAD_HOLD_ALL_SPEC;
impl crate::RegisterSpec for IMM_PAD_HOLD_ALL_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`imm_pad_hold_all::W`](W) writer structure"]
impl crate::Writable for IMM_PAD_HOLD_ALL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IMM_PAD_HOLD_ALL to value 0"]
impl crate::Resettable for IMM_PAD_HOLD_ALL_SPEC {}
