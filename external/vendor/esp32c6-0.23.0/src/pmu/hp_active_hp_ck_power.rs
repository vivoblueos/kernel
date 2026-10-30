#[doc = "Register `HP_ACTIVE_HP_CK_POWER` reader"]
pub type R = crate::R<HP_ACTIVE_HP_CK_POWER_SPEC>;
#[doc = "Register `HP_ACTIVE_HP_CK_POWER` writer"]
pub type W = crate::W<HP_ACTIVE_HP_CK_POWER_SPEC>;
#[doc = "Field `HP_ACTIVE_I2C_ISO_EN` reader - need_des"]
pub type HP_ACTIVE_I2C_ISO_EN_R = crate::BitReader;
#[doc = "Field `HP_ACTIVE_I2C_ISO_EN` writer - need_des"]
pub type HP_ACTIVE_I2C_ISO_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_ACTIVE_I2C_RETENTION` reader - need_des"]
pub type HP_ACTIVE_I2C_RETENTION_R = crate::BitReader;
#[doc = "Field `HP_ACTIVE_I2C_RETENTION` writer - need_des"]
pub type HP_ACTIVE_I2C_RETENTION_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_ACTIVE_XPD_BB_I2C` reader - need_des"]
pub type HP_ACTIVE_XPD_BB_I2C_R = crate::BitReader;
#[doc = "Field `HP_ACTIVE_XPD_BB_I2C` writer - need_des"]
pub type HP_ACTIVE_XPD_BB_I2C_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_ACTIVE_XPD_BBPLL_I2C` reader - need_des"]
pub type HP_ACTIVE_XPD_BBPLL_I2C_R = crate::BitReader;
#[doc = "Field `HP_ACTIVE_XPD_BBPLL_I2C` writer - need_des"]
pub type HP_ACTIVE_XPD_BBPLL_I2C_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_ACTIVE_XPD_BBPLL` reader - need_des"]
pub type HP_ACTIVE_XPD_BBPLL_R = crate::BitReader;
#[doc = "Field `HP_ACTIVE_XPD_BBPLL` writer - need_des"]
pub type HP_ACTIVE_XPD_BBPLL_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 26 - need_des"]
    #[inline(always)]
    pub fn hp_active_i2c_iso_en(&self) -> HP_ACTIVE_I2C_ISO_EN_R {
        HP_ACTIVE_I2C_ISO_EN_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn hp_active_i2c_retention(&self) -> HP_ACTIVE_I2C_RETENTION_R {
        HP_ACTIVE_I2C_RETENTION_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn hp_active_xpd_bb_i2c(&self) -> HP_ACTIVE_XPD_BB_I2C_R {
        HP_ACTIVE_XPD_BB_I2C_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn hp_active_xpd_bbpll_i2c(&self) -> HP_ACTIVE_XPD_BBPLL_I2C_R {
        HP_ACTIVE_XPD_BBPLL_I2C_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn hp_active_xpd_bbpll(&self) -> HP_ACTIVE_XPD_BBPLL_R {
        HP_ACTIVE_XPD_BBPLL_R::new(((self.bits >> 30) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HP_ACTIVE_HP_CK_POWER")
            .field("hp_active_i2c_iso_en", &self.hp_active_i2c_iso_en())
            .field("hp_active_i2c_retention", &self.hp_active_i2c_retention())
            .field("hp_active_xpd_bb_i2c", &self.hp_active_xpd_bb_i2c())
            .field("hp_active_xpd_bbpll_i2c", &self.hp_active_xpd_bbpll_i2c())
            .field("hp_active_xpd_bbpll", &self.hp_active_xpd_bbpll())
            .finish()
    }
}
impl W {
    #[doc = "Bit 26 - need_des"]
    #[inline(always)]
    pub fn hp_active_i2c_iso_en(
        &mut self,
    ) -> HP_ACTIVE_I2C_ISO_EN_W<'_, HP_ACTIVE_HP_CK_POWER_SPEC> {
        HP_ACTIVE_I2C_ISO_EN_W::new(self, 26)
    }
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn hp_active_i2c_retention(
        &mut self,
    ) -> HP_ACTIVE_I2C_RETENTION_W<'_, HP_ACTIVE_HP_CK_POWER_SPEC> {
        HP_ACTIVE_I2C_RETENTION_W::new(self, 27)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn hp_active_xpd_bb_i2c(
        &mut self,
    ) -> HP_ACTIVE_XPD_BB_I2C_W<'_, HP_ACTIVE_HP_CK_POWER_SPEC> {
        HP_ACTIVE_XPD_BB_I2C_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn hp_active_xpd_bbpll_i2c(
        &mut self,
    ) -> HP_ACTIVE_XPD_BBPLL_I2C_W<'_, HP_ACTIVE_HP_CK_POWER_SPEC> {
        HP_ACTIVE_XPD_BBPLL_I2C_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn hp_active_xpd_bbpll(&mut self) -> HP_ACTIVE_XPD_BBPLL_W<'_, HP_ACTIVE_HP_CK_POWER_SPEC> {
        HP_ACTIVE_XPD_BBPLL_W::new(self, 30)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_active_hp_ck_power::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hp_active_hp_ck_power::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_ACTIVE_HP_CK_POWER_SPEC;
impl crate::RegisterSpec for HP_ACTIVE_HP_CK_POWER_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hp_active_hp_ck_power::R`](R) reader structure"]
impl crate::Readable for HP_ACTIVE_HP_CK_POWER_SPEC {}
#[doc = "`write(|w| ..)` method takes [`hp_active_hp_ck_power::W`](W) writer structure"]
impl crate::Writable for HP_ACTIVE_HP_CK_POWER_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HP_ACTIVE_HP_CK_POWER to value 0"]
impl crate::Resettable for HP_ACTIVE_HP_CK_POWER_SPEC {}
