#[doc = "Register `BACKUP_BUS_PMS_CONSTRAIN_3` reader"]
pub type R = crate::R<BACKUP_BUS_PMS_CONSTRAIN_3_SPEC>;
#[doc = "Register `BACKUP_BUS_PMS_CONSTRAIN_3` writer"]
pub type W = crate::W<BACKUP_BUS_PMS_CONSTRAIN_3_SPEC>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_SPI_2` reader - backup_bus_pms_constrain_spi_2"]
pub type BACKUP_BUS_PMS_CONSTRAIN_SPI_2_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_SPI_2` writer - backup_bus_pms_constrain_spi_2"]
pub type BACKUP_BUS_PMS_CONSTRAIN_SPI_2_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_APB_CTRL` reader - backup_bus_pms_constrain_apb_ctrl"]
pub type BACKUP_BUS_PMS_CONSTRAIN_APB_CTRL_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_APB_CTRL` writer - backup_bus_pms_constrain_apb_ctrl"]
pub type BACKUP_BUS_PMS_CONSTRAIN_APB_CTRL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_CAN` reader - backup_bus_pms_constrain_can"]
pub type BACKUP_BUS_PMS_CONSTRAIN_CAN_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_CAN` writer - backup_bus_pms_constrain_can"]
pub type BACKUP_BUS_PMS_CONSTRAIN_CAN_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_I2S1` reader - backup_bus_pms_constrain_i2s1"]
pub type BACKUP_BUS_PMS_CONSTRAIN_I2S1_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_I2S1` writer - backup_bus_pms_constrain_i2s1"]
pub type BACKUP_BUS_PMS_CONSTRAIN_I2S1_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_RWBT` reader - backup_bus_pms_constrain_rwbt"]
pub type BACKUP_BUS_PMS_CONSTRAIN_RWBT_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_RWBT` writer - backup_bus_pms_constrain_rwbt"]
pub type BACKUP_BUS_PMS_CONSTRAIN_RWBT_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_WIFIMAC` reader - backup_bus_pms_constrain_wifimac"]
pub type BACKUP_BUS_PMS_CONSTRAIN_WIFIMAC_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_WIFIMAC` writer - backup_bus_pms_constrain_wifimac"]
pub type BACKUP_BUS_PMS_CONSTRAIN_WIFIMAC_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_PWR` reader - backup_bus_pms_constrain_pwr"]
pub type BACKUP_BUS_PMS_CONSTRAIN_PWR_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_PWR` writer - backup_bus_pms_constrain_pwr"]
pub type BACKUP_BUS_PMS_CONSTRAIN_PWR_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - backup_bus_pms_constrain_spi_2"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_spi_2(&self) -> BACKUP_BUS_PMS_CONSTRAIN_SPI_2_R {
        BACKUP_BUS_PMS_CONSTRAIN_SPI_2_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 4:5 - backup_bus_pms_constrain_apb_ctrl"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_apb_ctrl(&self) -> BACKUP_BUS_PMS_CONSTRAIN_APB_CTRL_R {
        BACKUP_BUS_PMS_CONSTRAIN_APB_CTRL_R::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bits 10:11 - backup_bus_pms_constrain_can"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_can(&self) -> BACKUP_BUS_PMS_CONSTRAIN_CAN_R {
        BACKUP_BUS_PMS_CONSTRAIN_CAN_R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bits 14:15 - backup_bus_pms_constrain_i2s1"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_i2s1(&self) -> BACKUP_BUS_PMS_CONSTRAIN_I2S1_R {
        BACKUP_BUS_PMS_CONSTRAIN_I2S1_R::new(((self.bits >> 14) & 3) as u8)
    }
    #[doc = "Bits 22:23 - backup_bus_pms_constrain_rwbt"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_rwbt(&self) -> BACKUP_BUS_PMS_CONSTRAIN_RWBT_R {
        BACKUP_BUS_PMS_CONSTRAIN_RWBT_R::new(((self.bits >> 22) & 3) as u8)
    }
    #[doc = "Bits 26:27 - backup_bus_pms_constrain_wifimac"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_wifimac(&self) -> BACKUP_BUS_PMS_CONSTRAIN_WIFIMAC_R {
        BACKUP_BUS_PMS_CONSTRAIN_WIFIMAC_R::new(((self.bits >> 26) & 3) as u8)
    }
    #[doc = "Bits 28:29 - backup_bus_pms_constrain_pwr"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_pwr(&self) -> BACKUP_BUS_PMS_CONSTRAIN_PWR_R {
        BACKUP_BUS_PMS_CONSTRAIN_PWR_R::new(((self.bits >> 28) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BACKUP_BUS_PMS_CONSTRAIN_3")
            .field(
                "backup_bus_pms_constrain_spi_2",
                &self.backup_bus_pms_constrain_spi_2(),
            )
            .field(
                "backup_bus_pms_constrain_apb_ctrl",
                &self.backup_bus_pms_constrain_apb_ctrl(),
            )
            .field(
                "backup_bus_pms_constrain_can",
                &self.backup_bus_pms_constrain_can(),
            )
            .field(
                "backup_bus_pms_constrain_i2s1",
                &self.backup_bus_pms_constrain_i2s1(),
            )
            .field(
                "backup_bus_pms_constrain_rwbt",
                &self.backup_bus_pms_constrain_rwbt(),
            )
            .field(
                "backup_bus_pms_constrain_wifimac",
                &self.backup_bus_pms_constrain_wifimac(),
            )
            .field(
                "backup_bus_pms_constrain_pwr",
                &self.backup_bus_pms_constrain_pwr(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - backup_bus_pms_constrain_spi_2"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_spi_2(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_SPI_2_W<'_, BACKUP_BUS_PMS_CONSTRAIN_3_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_SPI_2_W::new(self, 0)
    }
    #[doc = "Bits 4:5 - backup_bus_pms_constrain_apb_ctrl"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_apb_ctrl(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_APB_CTRL_W<'_, BACKUP_BUS_PMS_CONSTRAIN_3_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_APB_CTRL_W::new(self, 4)
    }
    #[doc = "Bits 10:11 - backup_bus_pms_constrain_can"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_can(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_CAN_W<'_, BACKUP_BUS_PMS_CONSTRAIN_3_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_CAN_W::new(self, 10)
    }
    #[doc = "Bits 14:15 - backup_bus_pms_constrain_i2s1"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_i2s1(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_I2S1_W<'_, BACKUP_BUS_PMS_CONSTRAIN_3_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_I2S1_W::new(self, 14)
    }
    #[doc = "Bits 22:23 - backup_bus_pms_constrain_rwbt"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_rwbt(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_RWBT_W<'_, BACKUP_BUS_PMS_CONSTRAIN_3_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_RWBT_W::new(self, 22)
    }
    #[doc = "Bits 26:27 - backup_bus_pms_constrain_wifimac"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_wifimac(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_WIFIMAC_W<'_, BACKUP_BUS_PMS_CONSTRAIN_3_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_WIFIMAC_W::new(self, 26)
    }
    #[doc = "Bits 28:29 - backup_bus_pms_constrain_pwr"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_pwr(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_PWR_W<'_, BACKUP_BUS_PMS_CONSTRAIN_3_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_PWR_W::new(self, 28)
    }
}
#[doc = "SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_constrain_3::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`backup_bus_pms_constrain_3::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BACKUP_BUS_PMS_CONSTRAIN_3_SPEC;
impl crate::RegisterSpec for BACKUP_BUS_PMS_CONSTRAIN_3_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`backup_bus_pms_constrain_3::R`](R) reader structure"]
impl crate::Readable for BACKUP_BUS_PMS_CONSTRAIN_3_SPEC {}
#[doc = "`write(|w| ..)` method takes [`backup_bus_pms_constrain_3::W`](W) writer structure"]
impl crate::Writable for BACKUP_BUS_PMS_CONSTRAIN_3_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets BACKUP_BUS_PMS_CONSTRAIN_3 to value 0x3cc0_cc33"]
impl crate::Resettable for BACKUP_BUS_PMS_CONSTRAIN_3_SPEC {
    const RESET_VALUE: u32 = 0x3cc0_cc33;
}
