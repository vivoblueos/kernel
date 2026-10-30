#[doc = "Register `HP_SLEEP_LP_REGULATOR0` reader"]
pub type R = crate::R<HP_SLEEP_LP_REGULATOR0_SPEC>;
#[doc = "Register `HP_SLEEP_LP_REGULATOR0` writer"]
pub type W = crate::W<HP_SLEEP_LP_REGULATOR0_SPEC>;
#[doc = "Field `HP_SLEEP_LP_REGULATOR_SLP_XPD` reader - need_des"]
pub type HP_SLEEP_LP_REGULATOR_SLP_XPD_R = crate::BitReader;
#[doc = "Field `HP_SLEEP_LP_REGULATOR_SLP_XPD` writer - need_des"]
pub type HP_SLEEP_LP_REGULATOR_SLP_XPD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_SLEEP_LP_REGULATOR_XPD` reader - need_des"]
pub type HP_SLEEP_LP_REGULATOR_XPD_R = crate::BitReader;
#[doc = "Field `HP_SLEEP_LP_REGULATOR_XPD` writer - need_des"]
pub type HP_SLEEP_LP_REGULATOR_XPD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_SLEEP_LP_REGULATOR_SLP_DBIAS` reader - need_des"]
pub type HP_SLEEP_LP_REGULATOR_SLP_DBIAS_R = crate::FieldReader;
#[doc = "Field `HP_SLEEP_LP_REGULATOR_SLP_DBIAS` writer - need_des"]
pub type HP_SLEEP_LP_REGULATOR_SLP_DBIAS_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `HP_SLEEP_LP_REGULATOR_DBIAS` reader - need_des"]
pub type HP_SLEEP_LP_REGULATOR_DBIAS_R = crate::FieldReader;
#[doc = "Field `HP_SLEEP_LP_REGULATOR_DBIAS` writer - need_des"]
pub type HP_SLEEP_LP_REGULATOR_DBIAS_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
impl R {
    #[doc = "Bit 21 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_lp_regulator_slp_xpd(&self) -> HP_SLEEP_LP_REGULATOR_SLP_XPD_R {
        HP_SLEEP_LP_REGULATOR_SLP_XPD_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_lp_regulator_xpd(&self) -> HP_SLEEP_LP_REGULATOR_XPD_R {
        HP_SLEEP_LP_REGULATOR_XPD_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bits 23:26 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_lp_regulator_slp_dbias(&self) -> HP_SLEEP_LP_REGULATOR_SLP_DBIAS_R {
        HP_SLEEP_LP_REGULATOR_SLP_DBIAS_R::new(((self.bits >> 23) & 0x0f) as u8)
    }
    #[doc = "Bits 27:31 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_lp_regulator_dbias(&self) -> HP_SLEEP_LP_REGULATOR_DBIAS_R {
        HP_SLEEP_LP_REGULATOR_DBIAS_R::new(((self.bits >> 27) & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HP_SLEEP_LP_REGULATOR0")
            .field(
                "hp_sleep_lp_regulator_slp_xpd",
                &self.hp_sleep_lp_regulator_slp_xpd(),
            )
            .field(
                "hp_sleep_lp_regulator_xpd",
                &self.hp_sleep_lp_regulator_xpd(),
            )
            .field(
                "hp_sleep_lp_regulator_slp_dbias",
                &self.hp_sleep_lp_regulator_slp_dbias(),
            )
            .field(
                "hp_sleep_lp_regulator_dbias",
                &self.hp_sleep_lp_regulator_dbias(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 21 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_lp_regulator_slp_xpd(
        &mut self,
    ) -> HP_SLEEP_LP_REGULATOR_SLP_XPD_W<'_, HP_SLEEP_LP_REGULATOR0_SPEC> {
        HP_SLEEP_LP_REGULATOR_SLP_XPD_W::new(self, 21)
    }
    #[doc = "Bit 22 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_lp_regulator_xpd(
        &mut self,
    ) -> HP_SLEEP_LP_REGULATOR_XPD_W<'_, HP_SLEEP_LP_REGULATOR0_SPEC> {
        HP_SLEEP_LP_REGULATOR_XPD_W::new(self, 22)
    }
    #[doc = "Bits 23:26 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_lp_regulator_slp_dbias(
        &mut self,
    ) -> HP_SLEEP_LP_REGULATOR_SLP_DBIAS_W<'_, HP_SLEEP_LP_REGULATOR0_SPEC> {
        HP_SLEEP_LP_REGULATOR_SLP_DBIAS_W::new(self, 23)
    }
    #[doc = "Bits 27:31 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_lp_regulator_dbias(
        &mut self,
    ) -> HP_SLEEP_LP_REGULATOR_DBIAS_W<'_, HP_SLEEP_LP_REGULATOR0_SPEC> {
        HP_SLEEP_LP_REGULATOR_DBIAS_W::new(self, 27)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_sleep_lp_regulator0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hp_sleep_lp_regulator0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_SLEEP_LP_REGULATOR0_SPEC;
impl crate::RegisterSpec for HP_SLEEP_LP_REGULATOR0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hp_sleep_lp_regulator0::R`](R) reader structure"]
impl crate::Readable for HP_SLEEP_LP_REGULATOR0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`hp_sleep_lp_regulator0::W`](W) writer structure"]
impl crate::Writable for HP_SLEEP_LP_REGULATOR0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HP_SLEEP_LP_REGULATOR0 to value 0xc660_0000"]
impl crate::Resettable for HP_SLEEP_LP_REGULATOR0_SPEC {
    const RESET_VALUE: u32 = 0xc660_0000;
}
