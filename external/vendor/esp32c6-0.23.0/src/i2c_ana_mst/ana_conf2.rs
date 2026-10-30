#[doc = "Register `ANA_CONF2` reader"]
pub type R = crate::R<ANA_CONF2_SPEC>;
#[doc = "Register `ANA_CONF2` writer"]
pub type W = crate::W<ANA_CONF2_SPEC>;
#[doc = "Field `BIAS_MST_SEL` reader - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
pub type BIAS_MST_SEL_R = crate::BitReader;
#[doc = "Field `BIAS_MST_SEL` writer - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
pub type BIAS_MST_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BBPLL_MST_SEL` reader - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
pub type BBPLL_MST_SEL_R = crate::BitReader;
#[doc = "Field `BBPLL_MST_SEL` writer - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
pub type BBPLL_MST_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ULP_CAL_MST_SEL` reader - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
pub type ULP_CAL_MST_SEL_R = crate::BitReader;
#[doc = "Field `ULP_CAL_MST_SEL` writer - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
pub type ULP_CAL_MST_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAR_I2C_MST_SEL` reader - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
pub type SAR_I2C_MST_SEL_R = crate::BitReader;
#[doc = "Field `SAR_I2C_MST_SEL` writer - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
pub type SAR_I2C_MST_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DIG_REG_MST_SEL` reader - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
pub type DIG_REG_MST_SEL_R = crate::BitReader;
#[doc = "Field `DIG_REG_MST_SEL` writer - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
pub type DIG_REG_MST_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAR_FORCE_PU` reader - ?"]
pub type SAR_FORCE_PU_R = crate::BitReader;
#[doc = "Field `SAR_FORCE_PU` writer - ?"]
pub type SAR_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BBPLL_M` reader - Clear to enable BBPLL"]
pub type BBPLL_M_R = crate::BitReader;
#[doc = "Field `BBPLL_M` writer - Clear to enable BBPLL"]
pub type BBPLL_M_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAR_FORCE_PD` reader - ?"]
pub type SAR_FORCE_PD_R = crate::BitReader;
#[doc = "Field `SAR_FORCE_PD` writer - ?"]
pub type SAR_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STATUS` reader - ?"]
pub type STATUS_R = crate::FieldReader;
impl R {
    #[doc = "Bit 8 - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
    #[inline(always)]
    pub fn bias_mst_sel(&self) -> BIAS_MST_SEL_R {
        BIAS_MST_SEL_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
    #[inline(always)]
    pub fn bbpll_mst_sel(&self) -> BBPLL_MST_SEL_R {
        BBPLL_MST_SEL_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
    #[inline(always)]
    pub fn ulp_cal_mst_sel(&self) -> ULP_CAL_MST_SEL_R {
        ULP_CAL_MST_SEL_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
    #[inline(always)]
    pub fn sar_i2c_mst_sel(&self) -> SAR_I2C_MST_SEL_R {
        SAR_I2C_MST_SEL_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
    #[inline(always)]
    pub fn dig_reg_mst_sel(&self) -> DIG_REG_MST_SEL_R {
        DIG_REG_MST_SEL_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 16 - ?"]
    #[inline(always)]
    pub fn sar_force_pu(&self) -> SAR_FORCE_PU_R {
        SAR_FORCE_PU_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Clear to enable BBPLL"]
    #[inline(always)]
    pub fn bbpll_m(&self) -> BBPLL_M_R {
        BBPLL_M_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - ?"]
    #[inline(always)]
    pub fn sar_force_pd(&self) -> SAR_FORCE_PD_R {
        SAR_FORCE_PD_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bits 24:31 - ?"]
    #[inline(always)]
    pub fn status(&self) -> STATUS_R {
        STATUS_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ANA_CONF2")
            .field("bias_mst_sel", &self.bias_mst_sel())
            .field("bbpll_mst_sel", &self.bbpll_mst_sel())
            .field("ulp_cal_mst_sel", &self.ulp_cal_mst_sel())
            .field("sar_i2c_mst_sel", &self.sar_i2c_mst_sel())
            .field("dig_reg_mst_sel", &self.dig_reg_mst_sel())
            .field("sar_force_pd", &self.sar_force_pd())
            .field("bbpll_m", &self.bbpll_m())
            .field("sar_force_pu", &self.sar_force_pu())
            .field("status", &self.status())
            .finish()
    }
}
impl W {
    #[doc = "Bit 8 - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
    #[inline(always)]
    pub fn bias_mst_sel(&mut self) -> BIAS_MST_SEL_W<'_, ANA_CONF2_SPEC> {
        BIAS_MST_SEL_W::new(self, 8)
    }
    #[doc = "Bit 9 - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
    #[inline(always)]
    pub fn bbpll_mst_sel(&mut self) -> BBPLL_MST_SEL_W<'_, ANA_CONF2_SPEC> {
        BBPLL_MST_SEL_W::new(self, 9)
    }
    #[doc = "Bit 10 - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
    #[inline(always)]
    pub fn ulp_cal_mst_sel(&mut self) -> ULP_CAL_MST_SEL_W<'_, ANA_CONF2_SPEC> {
        ULP_CAL_MST_SEL_W::new(self, 10)
    }
    #[doc = "Bit 11 - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
    #[inline(always)]
    pub fn sar_i2c_mst_sel(&mut self) -> SAR_I2C_MST_SEL_W<'_, ANA_CONF2_SPEC> {
        SAR_I2C_MST_SEL_W::new(self, 11)
    }
    #[doc = "Bit 12 - Configures which I2C master the following analog modules uses. If the corresponding bit is set to 1, I2C0 master is used for communication; if set to 0, I2C1 master is used."]
    #[inline(always)]
    pub fn dig_reg_mst_sel(&mut self) -> DIG_REG_MST_SEL_W<'_, ANA_CONF2_SPEC> {
        DIG_REG_MST_SEL_W::new(self, 12)
    }
    #[doc = "Bit 16 - ?"]
    #[inline(always)]
    pub fn sar_force_pu(&mut self) -> SAR_FORCE_PU_W<'_, ANA_CONF2_SPEC> {
        SAR_FORCE_PU_W::new(self, 16)
    }
    #[doc = "Bit 17 - Clear to enable BBPLL"]
    #[inline(always)]
    pub fn bbpll_m(&mut self) -> BBPLL_M_W<'_, ANA_CONF2_SPEC> {
        BBPLL_M_W::new(self, 17)
    }
    #[doc = "Bit 18 - ?"]
    #[inline(always)]
    pub fn sar_force_pd(&mut self) -> SAR_FORCE_PD_W<'_, ANA_CONF2_SPEC> {
        SAR_FORCE_PD_W::new(self, 18)
    }
}
#[doc = "ANA_CONF2 register\n\nYou can [`read`](crate::Reg::read) this register and get [`ana_conf2::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ana_conf2::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ANA_CONF2_SPEC;
impl crate::RegisterSpec for ANA_CONF2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ana_conf2::R`](R) reader structure"]
impl crate::Readable for ANA_CONF2_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ana_conf2::W`](W) writer structure"]
impl crate::Writable for ANA_CONF2_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ANA_CONF2 to value 0"]
impl crate::Resettable for ANA_CONF2_SPEC {}
