#[doc = "Register `IMM_HP_APB_ICG` writer"]
pub type W = crate::W<IMM_HP_APB_ICG_SPEC>;
#[doc = "Field `UPDATE_DIG_ICG_APB_EN` writer - need_des"]
pub type UPDATE_DIG_ICG_APB_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<IMM_HP_APB_ICG_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn update_dig_icg_apb_en(&mut self) -> UPDATE_DIG_ICG_APB_EN_W<'_, IMM_HP_APB_ICG_SPEC> {
        UPDATE_DIG_ICG_APB_EN_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`imm_hp_apb_icg::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IMM_HP_APB_ICG_SPEC;
impl crate::RegisterSpec for IMM_HP_APB_ICG_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`imm_hp_apb_icg::W`](W) writer structure"]
impl crate::Writable for IMM_HP_APB_ICG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IMM_HP_APB_ICG to value 0"]
impl crate::Resettable for IMM_HP_APB_ICG_SPEC {}
