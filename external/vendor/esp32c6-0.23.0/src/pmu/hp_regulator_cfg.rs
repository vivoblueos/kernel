#[doc = "Register `HP_REGULATOR_CFG` reader"]
pub type R = crate::R<HP_REGULATOR_CFG_SPEC>;
#[doc = "Register `HP_REGULATOR_CFG` writer"]
pub type W = crate::W<HP_REGULATOR_CFG_SPEC>;
#[doc = "Field `DIG_REGULATOR_EN_CAL` reader - need_des"]
pub type DIG_REGULATOR_EN_CAL_R = crate::BitReader;
#[doc = "Field `DIG_REGULATOR_EN_CAL` writer - need_des"]
pub type DIG_REGULATOR_EN_CAL_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn dig_regulator_en_cal(&self) -> DIG_REGULATOR_EN_CAL_R {
        DIG_REGULATOR_EN_CAL_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HP_REGULATOR_CFG")
            .field("dig_regulator_en_cal", &self.dig_regulator_en_cal())
            .finish()
    }
}
impl W {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn dig_regulator_en_cal(&mut self) -> DIG_REGULATOR_EN_CAL_W<'_, HP_REGULATOR_CFG_SPEC> {
        DIG_REGULATOR_EN_CAL_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_regulator_cfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hp_regulator_cfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_REGULATOR_CFG_SPEC;
impl crate::RegisterSpec for HP_REGULATOR_CFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hp_regulator_cfg::R`](R) reader structure"]
impl crate::Readable for HP_REGULATOR_CFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`hp_regulator_cfg::W`](W) writer structure"]
impl crate::Writable for HP_REGULATOR_CFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HP_REGULATOR_CFG to value 0"]
impl crate::Resettable for HP_REGULATOR_CFG_SPEC {}
