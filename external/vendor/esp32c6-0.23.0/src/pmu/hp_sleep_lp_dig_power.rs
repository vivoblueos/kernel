#[doc = "Register `HP_SLEEP_LP_DIG_POWER` reader"]
pub type R = crate::R<HP_SLEEP_LP_DIG_POWER_SPEC>;
#[doc = "Register `HP_SLEEP_LP_DIG_POWER` writer"]
pub type W = crate::W<HP_SLEEP_LP_DIG_POWER_SPEC>;
#[doc = "Field `HP_SLEEP_LP_MEM_DSLP` reader - need_des"]
pub type HP_SLEEP_LP_MEM_DSLP_R = crate::BitReader;
#[doc = "Field `HP_SLEEP_LP_MEM_DSLP` writer - need_des"]
pub type HP_SLEEP_LP_MEM_DSLP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_SLEEP_PD_LP_PERI_PD_EN` reader - need_des"]
pub type HP_SLEEP_PD_LP_PERI_PD_EN_R = crate::BitReader;
#[doc = "Field `HP_SLEEP_PD_LP_PERI_PD_EN` writer - need_des"]
pub type HP_SLEEP_PD_LP_PERI_PD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_lp_mem_dslp(&self) -> HP_SLEEP_LP_MEM_DSLP_R {
        HP_SLEEP_LP_MEM_DSLP_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_pd_lp_peri_pd_en(&self) -> HP_SLEEP_PD_LP_PERI_PD_EN_R {
        HP_SLEEP_PD_LP_PERI_PD_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HP_SLEEP_LP_DIG_POWER")
            .field("hp_sleep_lp_mem_dslp", &self.hp_sleep_lp_mem_dslp())
            .field(
                "hp_sleep_pd_lp_peri_pd_en",
                &self.hp_sleep_pd_lp_peri_pd_en(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_lp_mem_dslp(
        &mut self,
    ) -> HP_SLEEP_LP_MEM_DSLP_W<'_, HP_SLEEP_LP_DIG_POWER_SPEC> {
        HP_SLEEP_LP_MEM_DSLP_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn hp_sleep_pd_lp_peri_pd_en(
        &mut self,
    ) -> HP_SLEEP_PD_LP_PERI_PD_EN_W<'_, HP_SLEEP_LP_DIG_POWER_SPEC> {
        HP_SLEEP_PD_LP_PERI_PD_EN_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_sleep_lp_dig_power::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hp_sleep_lp_dig_power::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_SLEEP_LP_DIG_POWER_SPEC;
impl crate::RegisterSpec for HP_SLEEP_LP_DIG_POWER_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hp_sleep_lp_dig_power::R`](R) reader structure"]
impl crate::Readable for HP_SLEEP_LP_DIG_POWER_SPEC {}
#[doc = "`write(|w| ..)` method takes [`hp_sleep_lp_dig_power::W`](W) writer structure"]
impl crate::Writable for HP_SLEEP_LP_DIG_POWER_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HP_SLEEP_LP_DIG_POWER to value 0"]
impl crate::Resettable for HP_SLEEP_LP_DIG_POWER_SPEC {}
