#[doc = "Register `ANA_CONF1` reader"]
pub type R = crate::R<ANA_CONF1_SPEC>;
#[doc = "Register `ANA_CONF1` writer"]
pub type W = crate::W<ANA_CONF1_SPEC>;
#[doc = "Field `BIAS_RD` reader - Clear to select"]
pub type BIAS_RD_R = crate::BitReader;
#[doc = "Field `BIAS_RD` writer - Clear to select"]
pub type BIAS_RD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BBPLL_RD` reader - Clear to select"]
pub type BBPLL_RD_R = crate::BitReader;
#[doc = "Field `BBPLL_RD` writer - Clear to select"]
pub type BBPLL_RD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ULP_CAL_RD` reader - Clear to select"]
pub type ULP_CAL_RD_R = crate::BitReader;
#[doc = "Field `ULP_CAL_RD` writer - Clear to select"]
pub type ULP_CAL_RD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAR_I2C_RD` reader - Clear to select"]
pub type SAR_I2C_RD_R = crate::BitReader;
#[doc = "Field `SAR_I2C_RD` writer - Clear to select"]
pub type SAR_I2C_RD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DIG_REG_RD` reader - Clear to select"]
pub type DIG_REG_RD_R = crate::BitReader;
#[doc = "Field `DIG_REG_RD` writer - Clear to select"]
pub type DIG_REG_RD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAR_FORCE_PU` reader - ?"]
pub type SAR_FORCE_PU_R = crate::BitReader;
#[doc = "Field `SAR_FORCE_PU` writer - ?"]
pub type SAR_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BBPLL_PD` reader - Clear to enable BBPLL"]
pub type BBPLL_PD_R = crate::BitReader;
#[doc = "Field `BBPLL_PD` writer - Clear to enable BBPLL"]
pub type BBPLL_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAR_FORCE_PD` reader - ?"]
pub type SAR_FORCE_PD_R = crate::BitReader;
#[doc = "Field `SAR_FORCE_PD` writer - ?"]
pub type SAR_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STATUS` reader - ?"]
pub type STATUS_R = crate::FieldReader;
impl R {
    #[doc = "Bit 6 - Clear to select"]
    #[inline(always)]
    pub fn bias_rd(&self) -> BIAS_RD_R {
        BIAS_RD_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Clear to select"]
    #[inline(always)]
    pub fn bbpll_rd(&self) -> BBPLL_RD_R {
        BBPLL_RD_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Clear to select"]
    #[inline(always)]
    pub fn ulp_cal_rd(&self) -> ULP_CAL_RD_R {
        ULP_CAL_RD_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Clear to select"]
    #[inline(always)]
    pub fn sar_i2c_rd(&self) -> SAR_I2C_RD_R {
        SAR_I2C_RD_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Clear to select"]
    #[inline(always)]
    pub fn dig_reg_rd(&self) -> DIG_REG_RD_R {
        DIG_REG_RD_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 16 - ?"]
    #[inline(always)]
    pub fn sar_force_pu(&self) -> SAR_FORCE_PU_R {
        SAR_FORCE_PU_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Clear to enable BBPLL"]
    #[inline(always)]
    pub fn bbpll_pd(&self) -> BBPLL_PD_R {
        BBPLL_PD_R::new(((self.bits >> 17) & 1) != 0)
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
        f.debug_struct("ANA_CONF1")
            .field("bias_rd", &self.bias_rd())
            .field("bbpll_rd", &self.bbpll_rd())
            .field("ulp_cal_rd", &self.ulp_cal_rd())
            .field("sar_i2c_rd", &self.sar_i2c_rd())
            .field("dig_reg_rd", &self.dig_reg_rd())
            .field("bbpll_pd", &self.bbpll_pd())
            .field("sar_force_pd", &self.sar_force_pd())
            .field("sar_force_pu", &self.sar_force_pu())
            .field("status", &self.status())
            .finish()
    }
}
impl W {
    #[doc = "Bit 6 - Clear to select"]
    #[inline(always)]
    pub fn bias_rd(&mut self) -> BIAS_RD_W<'_, ANA_CONF1_SPEC> {
        BIAS_RD_W::new(self, 6)
    }
    #[doc = "Bit 7 - Clear to select"]
    #[inline(always)]
    pub fn bbpll_rd(&mut self) -> BBPLL_RD_W<'_, ANA_CONF1_SPEC> {
        BBPLL_RD_W::new(self, 7)
    }
    #[doc = "Bit 8 - Clear to select"]
    #[inline(always)]
    pub fn ulp_cal_rd(&mut self) -> ULP_CAL_RD_W<'_, ANA_CONF1_SPEC> {
        ULP_CAL_RD_W::new(self, 8)
    }
    #[doc = "Bit 9 - Clear to select"]
    #[inline(always)]
    pub fn sar_i2c_rd(&mut self) -> SAR_I2C_RD_W<'_, ANA_CONF1_SPEC> {
        SAR_I2C_RD_W::new(self, 9)
    }
    #[doc = "Bit 10 - Clear to select"]
    #[inline(always)]
    pub fn dig_reg_rd(&mut self) -> DIG_REG_RD_W<'_, ANA_CONF1_SPEC> {
        DIG_REG_RD_W::new(self, 10)
    }
    #[doc = "Bit 16 - ?"]
    #[inline(always)]
    pub fn sar_force_pu(&mut self) -> SAR_FORCE_PU_W<'_, ANA_CONF1_SPEC> {
        SAR_FORCE_PU_W::new(self, 16)
    }
    #[doc = "Bit 17 - Clear to enable BBPLL"]
    #[inline(always)]
    pub fn bbpll_pd(&mut self) -> BBPLL_PD_W<'_, ANA_CONF1_SPEC> {
        BBPLL_PD_W::new(self, 17)
    }
    #[doc = "Bit 18 - ?"]
    #[inline(always)]
    pub fn sar_force_pd(&mut self) -> SAR_FORCE_PD_W<'_, ANA_CONF1_SPEC> {
        SAR_FORCE_PD_W::new(self, 18)
    }
}
#[doc = "ANA_CONF1 register\n\nYou can [`read`](crate::Reg::read) this register and get [`ana_conf1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ana_conf1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ANA_CONF1_SPEC;
impl crate::RegisterSpec for ANA_CONF1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ana_conf1::R`](R) reader structure"]
impl crate::Readable for ANA_CONF1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ana_conf1::W`](W) writer structure"]
impl crate::Writable for ANA_CONF1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ANA_CONF1 to value 0"]
impl crate::Resettable for ANA_CONF1_SPEC {}
