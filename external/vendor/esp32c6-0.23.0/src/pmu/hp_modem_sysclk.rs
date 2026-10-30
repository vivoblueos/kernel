#[doc = "Register `HP_MODEM_SYSCLK` reader"]
pub type R = crate::R<HP_MODEM_SYSCLK_SPEC>;
#[doc = "Register `HP_MODEM_SYSCLK` writer"]
pub type W = crate::W<HP_MODEM_SYSCLK_SPEC>;
#[doc = "Field `HP_MODEM_DIG_SYS_CLK_NO_DIV` reader - need_des"]
pub type HP_MODEM_DIG_SYS_CLK_NO_DIV_R = crate::BitReader;
#[doc = "Field `HP_MODEM_DIG_SYS_CLK_NO_DIV` writer - need_des"]
pub type HP_MODEM_DIG_SYS_CLK_NO_DIV_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_MODEM_ICG_SYS_CLOCK_EN` reader - need_des"]
pub type HP_MODEM_ICG_SYS_CLOCK_EN_R = crate::BitReader;
#[doc = "Field `HP_MODEM_ICG_SYS_CLOCK_EN` writer - need_des"]
pub type HP_MODEM_ICG_SYS_CLOCK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_MODEM_SYS_CLK_SLP_SEL` reader - need_des"]
pub type HP_MODEM_SYS_CLK_SLP_SEL_R = crate::BitReader;
#[doc = "Field `HP_MODEM_SYS_CLK_SLP_SEL` writer - need_des"]
pub type HP_MODEM_SYS_CLK_SLP_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_MODEM_ICG_SLP_SEL` reader - need_des"]
pub type HP_MODEM_ICG_SLP_SEL_R = crate::BitReader;
#[doc = "Field `HP_MODEM_ICG_SLP_SEL` writer - need_des"]
pub type HP_MODEM_ICG_SLP_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_MODEM_DIG_SYS_CLK_SEL` reader - need_des"]
pub type HP_MODEM_DIG_SYS_CLK_SEL_R = crate::FieldReader;
#[doc = "Field `HP_MODEM_DIG_SYS_CLK_SEL` writer - need_des"]
pub type HP_MODEM_DIG_SYS_CLK_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bit 26 - need_des"]
    #[inline(always)]
    pub fn hp_modem_dig_sys_clk_no_div(&self) -> HP_MODEM_DIG_SYS_CLK_NO_DIV_R {
        HP_MODEM_DIG_SYS_CLK_NO_DIV_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn hp_modem_icg_sys_clock_en(&self) -> HP_MODEM_ICG_SYS_CLOCK_EN_R {
        HP_MODEM_ICG_SYS_CLOCK_EN_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn hp_modem_sys_clk_slp_sel(&self) -> HP_MODEM_SYS_CLK_SLP_SEL_R {
        HP_MODEM_SYS_CLK_SLP_SEL_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn hp_modem_icg_slp_sel(&self) -> HP_MODEM_ICG_SLP_SEL_R {
        HP_MODEM_ICG_SLP_SEL_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bits 30:31 - need_des"]
    #[inline(always)]
    pub fn hp_modem_dig_sys_clk_sel(&self) -> HP_MODEM_DIG_SYS_CLK_SEL_R {
        HP_MODEM_DIG_SYS_CLK_SEL_R::new(((self.bits >> 30) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HP_MODEM_SYSCLK")
            .field(
                "hp_modem_dig_sys_clk_no_div",
                &self.hp_modem_dig_sys_clk_no_div(),
            )
            .field(
                "hp_modem_icg_sys_clock_en",
                &self.hp_modem_icg_sys_clock_en(),
            )
            .field("hp_modem_sys_clk_slp_sel", &self.hp_modem_sys_clk_slp_sel())
            .field("hp_modem_icg_slp_sel", &self.hp_modem_icg_slp_sel())
            .field("hp_modem_dig_sys_clk_sel", &self.hp_modem_dig_sys_clk_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bit 26 - need_des"]
    #[inline(always)]
    pub fn hp_modem_dig_sys_clk_no_div(
        &mut self,
    ) -> HP_MODEM_DIG_SYS_CLK_NO_DIV_W<'_, HP_MODEM_SYSCLK_SPEC> {
        HP_MODEM_DIG_SYS_CLK_NO_DIV_W::new(self, 26)
    }
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn hp_modem_icg_sys_clock_en(
        &mut self,
    ) -> HP_MODEM_ICG_SYS_CLOCK_EN_W<'_, HP_MODEM_SYSCLK_SPEC> {
        HP_MODEM_ICG_SYS_CLOCK_EN_W::new(self, 27)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn hp_modem_sys_clk_slp_sel(
        &mut self,
    ) -> HP_MODEM_SYS_CLK_SLP_SEL_W<'_, HP_MODEM_SYSCLK_SPEC> {
        HP_MODEM_SYS_CLK_SLP_SEL_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn hp_modem_icg_slp_sel(&mut self) -> HP_MODEM_ICG_SLP_SEL_W<'_, HP_MODEM_SYSCLK_SPEC> {
        HP_MODEM_ICG_SLP_SEL_W::new(self, 29)
    }
    #[doc = "Bits 30:31 - need_des"]
    #[inline(always)]
    pub fn hp_modem_dig_sys_clk_sel(
        &mut self,
    ) -> HP_MODEM_DIG_SYS_CLK_SEL_W<'_, HP_MODEM_SYSCLK_SPEC> {
        HP_MODEM_DIG_SYS_CLK_SEL_W::new(self, 30)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_modem_sysclk::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hp_modem_sysclk::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_MODEM_SYSCLK_SPEC;
impl crate::RegisterSpec for HP_MODEM_SYSCLK_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hp_modem_sysclk::R`](R) reader structure"]
impl crate::Readable for HP_MODEM_SYSCLK_SPEC {}
#[doc = "`write(|w| ..)` method takes [`hp_modem_sysclk::W`](W) writer structure"]
impl crate::Writable for HP_MODEM_SYSCLK_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HP_MODEM_SYSCLK to value 0"]
impl crate::Resettable for HP_MODEM_SYSCLK_SPEC {}
