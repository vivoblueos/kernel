#[doc = "Register `HP_ACTIVE_DIG_POWER` reader"]
pub type R = crate::R<HP_ACTIVE_DIG_POWER_SPEC>;
#[doc = "Register `HP_ACTIVE_DIG_POWER` writer"]
pub type W = crate::W<HP_ACTIVE_DIG_POWER_SPEC>;
#[doc = "Field `HP_ACTIVE_VDD_SPI_PD_EN` reader - need_des"]
pub type HP_ACTIVE_VDD_SPI_PD_EN_R = crate::BitReader;
#[doc = "Field `HP_ACTIVE_VDD_SPI_PD_EN` writer - need_des"]
pub type HP_ACTIVE_VDD_SPI_PD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_ACTIVE_HP_MEM_DSLP` reader - need_des"]
pub type HP_ACTIVE_HP_MEM_DSLP_R = crate::BitReader;
#[doc = "Field `HP_ACTIVE_HP_MEM_DSLP` writer - need_des"]
pub type HP_ACTIVE_HP_MEM_DSLP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_ACTIVE_PD_HP_MEM_PD_EN` reader - need_des"]
pub type HP_ACTIVE_PD_HP_MEM_PD_EN_R = crate::FieldReader;
#[doc = "Field `HP_ACTIVE_PD_HP_MEM_PD_EN` writer - need_des"]
pub type HP_ACTIVE_PD_HP_MEM_PD_EN_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `HP_ACTIVE_PD_HP_WIFI_PD_EN` reader - need_des"]
pub type HP_ACTIVE_PD_HP_WIFI_PD_EN_R = crate::BitReader;
#[doc = "Field `HP_ACTIVE_PD_HP_WIFI_PD_EN` writer - need_des"]
pub type HP_ACTIVE_PD_HP_WIFI_PD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_ACTIVE_PD_HP_CPU_PD_EN` reader - need_des"]
pub type HP_ACTIVE_PD_HP_CPU_PD_EN_R = crate::BitReader;
#[doc = "Field `HP_ACTIVE_PD_HP_CPU_PD_EN` writer - need_des"]
pub type HP_ACTIVE_PD_HP_CPU_PD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_ACTIVE_PD_HP_AON_PD_EN` reader - need_des"]
pub type HP_ACTIVE_PD_HP_AON_PD_EN_R = crate::BitReader;
#[doc = "Field `HP_ACTIVE_PD_HP_AON_PD_EN` writer - need_des"]
pub type HP_ACTIVE_PD_HP_AON_PD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_ACTIVE_PD_TOP_PD_EN` reader - need_des"]
pub type HP_ACTIVE_PD_TOP_PD_EN_R = crate::BitReader;
#[doc = "Field `HP_ACTIVE_PD_TOP_PD_EN` writer - need_des"]
pub type HP_ACTIVE_PD_TOP_PD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 21 - need_des"]
    #[inline(always)]
    pub fn hp_active_vdd_spi_pd_en(&self) -> HP_ACTIVE_VDD_SPI_PD_EN_R {
        HP_ACTIVE_VDD_SPI_PD_EN_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - need_des"]
    #[inline(always)]
    pub fn hp_active_hp_mem_dslp(&self) -> HP_ACTIVE_HP_MEM_DSLP_R {
        HP_ACTIVE_HP_MEM_DSLP_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bits 23:26 - need_des"]
    #[inline(always)]
    pub fn hp_active_pd_hp_mem_pd_en(&self) -> HP_ACTIVE_PD_HP_MEM_PD_EN_R {
        HP_ACTIVE_PD_HP_MEM_PD_EN_R::new(((self.bits >> 23) & 0x0f) as u8)
    }
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn hp_active_pd_hp_wifi_pd_en(&self) -> HP_ACTIVE_PD_HP_WIFI_PD_EN_R {
        HP_ACTIVE_PD_HP_WIFI_PD_EN_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn hp_active_pd_hp_cpu_pd_en(&self) -> HP_ACTIVE_PD_HP_CPU_PD_EN_R {
        HP_ACTIVE_PD_HP_CPU_PD_EN_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn hp_active_pd_hp_aon_pd_en(&self) -> HP_ACTIVE_PD_HP_AON_PD_EN_R {
        HP_ACTIVE_PD_HP_AON_PD_EN_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn hp_active_pd_top_pd_en(&self) -> HP_ACTIVE_PD_TOP_PD_EN_R {
        HP_ACTIVE_PD_TOP_PD_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HP_ACTIVE_DIG_POWER")
            .field("hp_active_vdd_spi_pd_en", &self.hp_active_vdd_spi_pd_en())
            .field("hp_active_hp_mem_dslp", &self.hp_active_hp_mem_dslp())
            .field(
                "hp_active_pd_hp_mem_pd_en",
                &self.hp_active_pd_hp_mem_pd_en(),
            )
            .field(
                "hp_active_pd_hp_wifi_pd_en",
                &self.hp_active_pd_hp_wifi_pd_en(),
            )
            .field(
                "hp_active_pd_hp_cpu_pd_en",
                &self.hp_active_pd_hp_cpu_pd_en(),
            )
            .field(
                "hp_active_pd_hp_aon_pd_en",
                &self.hp_active_pd_hp_aon_pd_en(),
            )
            .field("hp_active_pd_top_pd_en", &self.hp_active_pd_top_pd_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 21 - need_des"]
    #[inline(always)]
    pub fn hp_active_vdd_spi_pd_en(
        &mut self,
    ) -> HP_ACTIVE_VDD_SPI_PD_EN_W<'_, HP_ACTIVE_DIG_POWER_SPEC> {
        HP_ACTIVE_VDD_SPI_PD_EN_W::new(self, 21)
    }
    #[doc = "Bit 22 - need_des"]
    #[inline(always)]
    pub fn hp_active_hp_mem_dslp(
        &mut self,
    ) -> HP_ACTIVE_HP_MEM_DSLP_W<'_, HP_ACTIVE_DIG_POWER_SPEC> {
        HP_ACTIVE_HP_MEM_DSLP_W::new(self, 22)
    }
    #[doc = "Bits 23:26 - need_des"]
    #[inline(always)]
    pub fn hp_active_pd_hp_mem_pd_en(
        &mut self,
    ) -> HP_ACTIVE_PD_HP_MEM_PD_EN_W<'_, HP_ACTIVE_DIG_POWER_SPEC> {
        HP_ACTIVE_PD_HP_MEM_PD_EN_W::new(self, 23)
    }
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn hp_active_pd_hp_wifi_pd_en(
        &mut self,
    ) -> HP_ACTIVE_PD_HP_WIFI_PD_EN_W<'_, HP_ACTIVE_DIG_POWER_SPEC> {
        HP_ACTIVE_PD_HP_WIFI_PD_EN_W::new(self, 27)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn hp_active_pd_hp_cpu_pd_en(
        &mut self,
    ) -> HP_ACTIVE_PD_HP_CPU_PD_EN_W<'_, HP_ACTIVE_DIG_POWER_SPEC> {
        HP_ACTIVE_PD_HP_CPU_PD_EN_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn hp_active_pd_hp_aon_pd_en(
        &mut self,
    ) -> HP_ACTIVE_PD_HP_AON_PD_EN_W<'_, HP_ACTIVE_DIG_POWER_SPEC> {
        HP_ACTIVE_PD_HP_AON_PD_EN_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn hp_active_pd_top_pd_en(
        &mut self,
    ) -> HP_ACTIVE_PD_TOP_PD_EN_W<'_, HP_ACTIVE_DIG_POWER_SPEC> {
        HP_ACTIVE_PD_TOP_PD_EN_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_active_dig_power::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hp_active_dig_power::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_ACTIVE_DIG_POWER_SPEC;
impl crate::RegisterSpec for HP_ACTIVE_DIG_POWER_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hp_active_dig_power::R`](R) reader structure"]
impl crate::Readable for HP_ACTIVE_DIG_POWER_SPEC {}
#[doc = "`write(|w| ..)` method takes [`hp_active_dig_power::W`](W) writer structure"]
impl crate::Writable for HP_ACTIVE_DIG_POWER_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HP_ACTIVE_DIG_POWER to value 0"]
impl crate::Resettable for HP_ACTIVE_DIG_POWER_SPEC {}
