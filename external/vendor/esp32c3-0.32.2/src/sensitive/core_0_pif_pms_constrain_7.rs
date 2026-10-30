#[doc = "Register `CORE_0_PIF_PMS_CONSTRAIN_7` reader"]
pub type R = crate::R<CORE_0_PIF_PMS_CONSTRAIN_7_SPEC>;
#[doc = "Register `CORE_0_PIF_PMS_CONSTRAIN_7` writer"]
pub type W = crate::W<CORE_0_PIF_PMS_CONSTRAIN_7_SPEC>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SPI_2` reader - core_0_pif_pms_constrain_world_1_spi_2"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SPI_2_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SPI_2` writer - core_0_pif_pms_constrain_world_1_spi_2"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SPI_2_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_APB_CTRL` reader - core_0_pif_pms_constrain_world_1_apb_ctrl"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_APB_CTRL_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_APB_CTRL` writer - core_0_pif_pms_constrain_world_1_apb_ctrl"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_APB_CTRL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_CAN` reader - core_0_pif_pms_constrain_world_1_can"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_CAN_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_CAN` writer - core_0_pif_pms_constrain_world_1_can"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_CAN_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2S1` reader - core_0_pif_pms_constrain_world_1_i2s1"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2S1_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2S1` writer - core_0_pif_pms_constrain_world_1_i2s1"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2S1_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RWBT` reader - core_0_pif_pms_constrain_world_1_rwbt"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RWBT_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RWBT` writer - core_0_pif_pms_constrain_world_1_rwbt"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RWBT_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_WIFIMAC` reader - core_0_pif_pms_constrain_world_1_wifimac"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_WIFIMAC_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_WIFIMAC` writer - core_0_pif_pms_constrain_world_1_wifimac"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_WIFIMAC_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_PWR` reader - core_0_pif_pms_constrain_world_1_pwr"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_PWR_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_PWR` writer - core_0_pif_pms_constrain_world_1_pwr"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_PWR_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - core_0_pif_pms_constrain_world_1_spi_2"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_spi_2(
        &self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SPI_2_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SPI_2_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 4:5 - core_0_pif_pms_constrain_world_1_apb_ctrl"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_apb_ctrl(
        &self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_APB_CTRL_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_APB_CTRL_R::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bits 10:11 - core_0_pif_pms_constrain_world_1_can"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_can(&self) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_CAN_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_CAN_R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bits 14:15 - core_0_pif_pms_constrain_world_1_i2s1"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_i2s1(&self) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2S1_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2S1_R::new(((self.bits >> 14) & 3) as u8)
    }
    #[doc = "Bits 22:23 - core_0_pif_pms_constrain_world_1_rwbt"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_rwbt(&self) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RWBT_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RWBT_R::new(((self.bits >> 22) & 3) as u8)
    }
    #[doc = "Bits 26:27 - core_0_pif_pms_constrain_world_1_wifimac"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_wifimac(
        &self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_WIFIMAC_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_WIFIMAC_R::new(((self.bits >> 26) & 3) as u8)
    }
    #[doc = "Bits 28:29 - core_0_pif_pms_constrain_world_1_pwr"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_pwr(&self) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_PWR_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_PWR_R::new(((self.bits >> 28) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE_0_PIF_PMS_CONSTRAIN_7")
            .field(
                "core_0_pif_pms_constrain_world_1_spi_2",
                &self.core_0_pif_pms_constrain_world_1_spi_2(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_apb_ctrl",
                &self.core_0_pif_pms_constrain_world_1_apb_ctrl(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_can",
                &self.core_0_pif_pms_constrain_world_1_can(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_i2s1",
                &self.core_0_pif_pms_constrain_world_1_i2s1(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_rwbt",
                &self.core_0_pif_pms_constrain_world_1_rwbt(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_wifimac",
                &self.core_0_pif_pms_constrain_world_1_wifimac(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_pwr",
                &self.core_0_pif_pms_constrain_world_1_pwr(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - core_0_pif_pms_constrain_world_1_spi_2"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_spi_2(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SPI_2_W<'_, CORE_0_PIF_PMS_CONSTRAIN_7_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SPI_2_W::new(self, 0)
    }
    #[doc = "Bits 4:5 - core_0_pif_pms_constrain_world_1_apb_ctrl"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_apb_ctrl(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_APB_CTRL_W<'_, CORE_0_PIF_PMS_CONSTRAIN_7_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_APB_CTRL_W::new(self, 4)
    }
    #[doc = "Bits 10:11 - core_0_pif_pms_constrain_world_1_can"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_can(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_CAN_W<'_, CORE_0_PIF_PMS_CONSTRAIN_7_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_CAN_W::new(self, 10)
    }
    #[doc = "Bits 14:15 - core_0_pif_pms_constrain_world_1_i2s1"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_i2s1(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2S1_W<'_, CORE_0_PIF_PMS_CONSTRAIN_7_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2S1_W::new(self, 14)
    }
    #[doc = "Bits 22:23 - core_0_pif_pms_constrain_world_1_rwbt"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_rwbt(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RWBT_W<'_, CORE_0_PIF_PMS_CONSTRAIN_7_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RWBT_W::new(self, 22)
    }
    #[doc = "Bits 26:27 - core_0_pif_pms_constrain_world_1_wifimac"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_wifimac(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_WIFIMAC_W<'_, CORE_0_PIF_PMS_CONSTRAIN_7_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_WIFIMAC_W::new(self, 26)
    }
    #[doc = "Bits 28:29 - core_0_pif_pms_constrain_world_1_pwr"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_pwr(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_PWR_W<'_, CORE_0_PIF_PMS_CONSTRAIN_7_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_PWR_W::new(self, 28)
    }
}
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_7_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_7::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_7::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE_0_PIF_PMS_CONSTRAIN_7_SPEC;
impl crate::RegisterSpec for CORE_0_PIF_PMS_CONSTRAIN_7_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core_0_pif_pms_constrain_7::R`](R) reader structure"]
impl crate::Readable for CORE_0_PIF_PMS_CONSTRAIN_7_SPEC {}
#[doc = "`write(|w| ..)` method takes [`core_0_pif_pms_constrain_7::W`](W) writer structure"]
impl crate::Writable for CORE_0_PIF_PMS_CONSTRAIN_7_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CORE_0_PIF_PMS_CONSTRAIN_7 to value 0x3cc0_cc33"]
impl crate::Resettable for CORE_0_PIF_PMS_CONSTRAIN_7_SPEC {
    const RESET_VALUE: u32 = 0x3cc0_cc33;
}
