#[doc = "Register `IMM_HP_CK_POWER` reader"]
pub type R = crate::R<IMM_HP_CK_POWER_SPEC>;
#[doc = "Register `IMM_HP_CK_POWER` writer"]
pub type W = crate::W<IMM_HP_CK_POWER_SPEC>;
#[doc = "Field `TIE_LOW_GLOBAL_BBPLL_ICG` writer - need_des"]
pub type TIE_LOW_GLOBAL_BBPLL_ICG_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_LOW_GLOBAL_XTAL_ICG` writer - need_des"]
pub type TIE_LOW_GLOBAL_XTAL_ICG_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_LOW_I2C_RETENTION` writer - need_des"]
pub type TIE_LOW_I2C_RETENTION_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_LOW_XPD_BB_I2C` writer - need_des"]
pub type TIE_LOW_XPD_BB_I2C_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_LOW_XPD_BBPLL_I2C` writer - need_des"]
pub type TIE_LOW_XPD_BBPLL_I2C_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_LOW_XPD_BBPLL` writer - need_des"]
pub type TIE_LOW_XPD_BBPLL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_LOW_XPD_XTAL` writer - need_des"]
pub type TIE_LOW_XPD_XTAL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_HIGH_GLOBAL_BBPLL_ICG` writer - need_des"]
pub type TIE_HIGH_GLOBAL_BBPLL_ICG_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_HIGH_GLOBAL_XTAL_ICG` writer - need_des"]
pub type TIE_HIGH_GLOBAL_XTAL_ICG_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_HIGH_I2C_RETENTION` writer - need_des"]
pub type TIE_HIGH_I2C_RETENTION_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_HIGH_XPD_BB_I2C` writer - need_des"]
pub type TIE_HIGH_XPD_BB_I2C_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_HIGH_XPD_BBPLL_I2C` writer - need_des"]
pub type TIE_HIGH_XPD_BBPLL_I2C_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_HIGH_XPD_BBPLL` writer - need_des"]
pub type TIE_HIGH_XPD_BBPLL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIE_HIGH_XPD_XTAL` writer - need_des"]
pub type TIE_HIGH_XPD_XTAL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IMM_HP_CK_POWER").finish()
    }
}
impl W {
    #[doc = "Bit 0 - need_des"]
    #[inline(always)]
    pub fn tie_low_global_bbpll_icg(
        &mut self,
    ) -> TIE_LOW_GLOBAL_BBPLL_ICG_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_LOW_GLOBAL_BBPLL_ICG_W::new(self, 0)
    }
    #[doc = "Bit 1 - need_des"]
    #[inline(always)]
    pub fn tie_low_global_xtal_icg(
        &mut self,
    ) -> TIE_LOW_GLOBAL_XTAL_ICG_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_LOW_GLOBAL_XTAL_ICG_W::new(self, 1)
    }
    #[doc = "Bit 2 - need_des"]
    #[inline(always)]
    pub fn tie_low_i2c_retention(&mut self) -> TIE_LOW_I2C_RETENTION_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_LOW_I2C_RETENTION_W::new(self, 2)
    }
    #[doc = "Bit 3 - need_des"]
    #[inline(always)]
    pub fn tie_low_xpd_bb_i2c(&mut self) -> TIE_LOW_XPD_BB_I2C_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_LOW_XPD_BB_I2C_W::new(self, 3)
    }
    #[doc = "Bit 4 - need_des"]
    #[inline(always)]
    pub fn tie_low_xpd_bbpll_i2c(&mut self) -> TIE_LOW_XPD_BBPLL_I2C_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_LOW_XPD_BBPLL_I2C_W::new(self, 4)
    }
    #[doc = "Bit 5 - need_des"]
    #[inline(always)]
    pub fn tie_low_xpd_bbpll(&mut self) -> TIE_LOW_XPD_BBPLL_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_LOW_XPD_BBPLL_W::new(self, 5)
    }
    #[doc = "Bit 6 - need_des"]
    #[inline(always)]
    pub fn tie_low_xpd_xtal(&mut self) -> TIE_LOW_XPD_XTAL_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_LOW_XPD_XTAL_W::new(self, 6)
    }
    #[doc = "Bit 25 - need_des"]
    #[inline(always)]
    pub fn tie_high_global_bbpll_icg(
        &mut self,
    ) -> TIE_HIGH_GLOBAL_BBPLL_ICG_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_HIGH_GLOBAL_BBPLL_ICG_W::new(self, 25)
    }
    #[doc = "Bit 26 - need_des"]
    #[inline(always)]
    pub fn tie_high_global_xtal_icg(
        &mut self,
    ) -> TIE_HIGH_GLOBAL_XTAL_ICG_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_HIGH_GLOBAL_XTAL_ICG_W::new(self, 26)
    }
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn tie_high_i2c_retention(&mut self) -> TIE_HIGH_I2C_RETENTION_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_HIGH_I2C_RETENTION_W::new(self, 27)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn tie_high_xpd_bb_i2c(&mut self) -> TIE_HIGH_XPD_BB_I2C_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_HIGH_XPD_BB_I2C_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn tie_high_xpd_bbpll_i2c(&mut self) -> TIE_HIGH_XPD_BBPLL_I2C_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_HIGH_XPD_BBPLL_I2C_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn tie_high_xpd_bbpll(&mut self) -> TIE_HIGH_XPD_BBPLL_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_HIGH_XPD_BBPLL_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn tie_high_xpd_xtal(&mut self) -> TIE_HIGH_XPD_XTAL_W<'_, IMM_HP_CK_POWER_SPEC> {
        TIE_HIGH_XPD_XTAL_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`imm_hp_ck_power::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`imm_hp_ck_power::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IMM_HP_CK_POWER_SPEC;
impl crate::RegisterSpec for IMM_HP_CK_POWER_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`imm_hp_ck_power::R`](R) reader structure"]
impl crate::Readable for IMM_HP_CK_POWER_SPEC {}
#[doc = "`write(|w| ..)` method takes [`imm_hp_ck_power::W`](W) writer structure"]
impl crate::Writable for IMM_HP_CK_POWER_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IMM_HP_CK_POWER to value 0"]
impl crate::Resettable for IMM_HP_CK_POWER_SPEC {}
