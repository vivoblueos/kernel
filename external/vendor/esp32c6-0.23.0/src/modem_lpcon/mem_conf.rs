#[doc = "Register `MEM_CONF` reader"]
pub type R = crate::R<MEM_CONF_SPEC>;
#[doc = "Register `MEM_CONF` writer"]
pub type W = crate::W<MEM_CONF_SPEC>;
#[doc = "Field `DC_MEM_FORCE_PU` reader - "]
pub type DC_MEM_FORCE_PU_R = crate::BitReader;
#[doc = "Field `DC_MEM_FORCE_PU` writer - "]
pub type DC_MEM_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DC_MEM_FORCE_PD` reader - "]
pub type DC_MEM_FORCE_PD_R = crate::BitReader;
#[doc = "Field `DC_MEM_FORCE_PD` writer - "]
pub type DC_MEM_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AGC_MEM_FORCE_PU` reader - "]
pub type AGC_MEM_FORCE_PU_R = crate::BitReader;
#[doc = "Field `AGC_MEM_FORCE_PU` writer - "]
pub type AGC_MEM_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AGC_MEM_FORCE_PD` reader - "]
pub type AGC_MEM_FORCE_PD_R = crate::BitReader;
#[doc = "Field `AGC_MEM_FORCE_PD` writer - "]
pub type AGC_MEM_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PBUS_MEM_FORCE_PU` reader - "]
pub type PBUS_MEM_FORCE_PU_R = crate::BitReader;
#[doc = "Field `PBUS_MEM_FORCE_PU` writer - "]
pub type PBUS_MEM_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PBUS_MEM_FORCE_PD` reader - "]
pub type PBUS_MEM_FORCE_PD_R = crate::BitReader;
#[doc = "Field `PBUS_MEM_FORCE_PD` writer - "]
pub type PBUS_MEM_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BC_MEM_FORCE_PU` reader - "]
pub type BC_MEM_FORCE_PU_R = crate::BitReader;
#[doc = "Field `BC_MEM_FORCE_PU` writer - "]
pub type BC_MEM_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BC_MEM_FORCE_PD` reader - "]
pub type BC_MEM_FORCE_PD_R = crate::BitReader;
#[doc = "Field `BC_MEM_FORCE_PD` writer - "]
pub type BC_MEM_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2C_MST_MEM_FORCE_PU` reader - "]
pub type I2C_MST_MEM_FORCE_PU_R = crate::BitReader;
#[doc = "Field `I2C_MST_MEM_FORCE_PU` writer - "]
pub type I2C_MST_MEM_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2C_MST_MEM_FORCE_PD` reader - "]
pub type I2C_MST_MEM_FORCE_PD_R = crate::BitReader;
#[doc = "Field `I2C_MST_MEM_FORCE_PD` writer - "]
pub type I2C_MST_MEM_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CHAN_FREQ_MEM_FORCE_PU` reader - "]
pub type CHAN_FREQ_MEM_FORCE_PU_R = crate::BitReader;
#[doc = "Field `CHAN_FREQ_MEM_FORCE_PU` writer - "]
pub type CHAN_FREQ_MEM_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CHAN_FREQ_MEM_FORCE_PD` reader - "]
pub type CHAN_FREQ_MEM_FORCE_PD_R = crate::BitReader;
#[doc = "Field `CHAN_FREQ_MEM_FORCE_PD` writer - "]
pub type CHAN_FREQ_MEM_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MODEM_PWR_MEM_WP` reader - "]
pub type MODEM_PWR_MEM_WP_R = crate::FieldReader;
#[doc = "Field `MODEM_PWR_MEM_WP` writer - "]
pub type MODEM_PWR_MEM_WP_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `MODEM_PWR_MEM_WA` reader - "]
pub type MODEM_PWR_MEM_WA_R = crate::FieldReader;
#[doc = "Field `MODEM_PWR_MEM_WA` writer - "]
pub type MODEM_PWR_MEM_WA_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `MODEM_PWR_MEM_RA` reader - "]
pub type MODEM_PWR_MEM_RA_R = crate::FieldReader;
#[doc = "Field `MODEM_PWR_MEM_RA` writer - "]
pub type MODEM_PWR_MEM_RA_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn dc_mem_force_pu(&self) -> DC_MEM_FORCE_PU_R {
        DC_MEM_FORCE_PU_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn dc_mem_force_pd(&self) -> DC_MEM_FORCE_PD_R {
        DC_MEM_FORCE_PD_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2"]
    #[inline(always)]
    pub fn agc_mem_force_pu(&self) -> AGC_MEM_FORCE_PU_R {
        AGC_MEM_FORCE_PU_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn agc_mem_force_pd(&self) -> AGC_MEM_FORCE_PD_R {
        AGC_MEM_FORCE_PD_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4"]
    #[inline(always)]
    pub fn pbus_mem_force_pu(&self) -> PBUS_MEM_FORCE_PU_R {
        PBUS_MEM_FORCE_PU_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5"]
    #[inline(always)]
    pub fn pbus_mem_force_pd(&self) -> PBUS_MEM_FORCE_PD_R {
        PBUS_MEM_FORCE_PD_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6"]
    #[inline(always)]
    pub fn bc_mem_force_pu(&self) -> BC_MEM_FORCE_PU_R {
        BC_MEM_FORCE_PU_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7"]
    #[inline(always)]
    pub fn bc_mem_force_pd(&self) -> BC_MEM_FORCE_PD_R {
        BC_MEM_FORCE_PD_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8"]
    #[inline(always)]
    pub fn i2c_mst_mem_force_pu(&self) -> I2C_MST_MEM_FORCE_PU_R {
        I2C_MST_MEM_FORCE_PU_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9"]
    #[inline(always)]
    pub fn i2c_mst_mem_force_pd(&self) -> I2C_MST_MEM_FORCE_PD_R {
        I2C_MST_MEM_FORCE_PD_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10"]
    #[inline(always)]
    pub fn chan_freq_mem_force_pu(&self) -> CHAN_FREQ_MEM_FORCE_PU_R {
        CHAN_FREQ_MEM_FORCE_PU_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11"]
    #[inline(always)]
    pub fn chan_freq_mem_force_pd(&self) -> CHAN_FREQ_MEM_FORCE_PD_R {
        CHAN_FREQ_MEM_FORCE_PD_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bits 12:14"]
    #[inline(always)]
    pub fn modem_pwr_mem_wp(&self) -> MODEM_PWR_MEM_WP_R {
        MODEM_PWR_MEM_WP_R::new(((self.bits >> 12) & 7) as u8)
    }
    #[doc = "Bits 15:17"]
    #[inline(always)]
    pub fn modem_pwr_mem_wa(&self) -> MODEM_PWR_MEM_WA_R {
        MODEM_PWR_MEM_WA_R::new(((self.bits >> 15) & 7) as u8)
    }
    #[doc = "Bits 18:19"]
    #[inline(always)]
    pub fn modem_pwr_mem_ra(&self) -> MODEM_PWR_MEM_RA_R {
        MODEM_PWR_MEM_RA_R::new(((self.bits >> 18) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MEM_CONF")
            .field("dc_mem_force_pu", &self.dc_mem_force_pu())
            .field("dc_mem_force_pd", &self.dc_mem_force_pd())
            .field("agc_mem_force_pu", &self.agc_mem_force_pu())
            .field("agc_mem_force_pd", &self.agc_mem_force_pd())
            .field("pbus_mem_force_pu", &self.pbus_mem_force_pu())
            .field("pbus_mem_force_pd", &self.pbus_mem_force_pd())
            .field("bc_mem_force_pu", &self.bc_mem_force_pu())
            .field("bc_mem_force_pd", &self.bc_mem_force_pd())
            .field("i2c_mst_mem_force_pu", &self.i2c_mst_mem_force_pu())
            .field("i2c_mst_mem_force_pd", &self.i2c_mst_mem_force_pd())
            .field("chan_freq_mem_force_pu", &self.chan_freq_mem_force_pu())
            .field("chan_freq_mem_force_pd", &self.chan_freq_mem_force_pd())
            .field("modem_pwr_mem_wp", &self.modem_pwr_mem_wp())
            .field("modem_pwr_mem_wa", &self.modem_pwr_mem_wa())
            .field("modem_pwr_mem_ra", &self.modem_pwr_mem_ra())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn dc_mem_force_pu(&mut self) -> DC_MEM_FORCE_PU_W<'_, MEM_CONF_SPEC> {
        DC_MEM_FORCE_PU_W::new(self, 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn dc_mem_force_pd(&mut self) -> DC_MEM_FORCE_PD_W<'_, MEM_CONF_SPEC> {
        DC_MEM_FORCE_PD_W::new(self, 1)
    }
    #[doc = "Bit 2"]
    #[inline(always)]
    pub fn agc_mem_force_pu(&mut self) -> AGC_MEM_FORCE_PU_W<'_, MEM_CONF_SPEC> {
        AGC_MEM_FORCE_PU_W::new(self, 2)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn agc_mem_force_pd(&mut self) -> AGC_MEM_FORCE_PD_W<'_, MEM_CONF_SPEC> {
        AGC_MEM_FORCE_PD_W::new(self, 3)
    }
    #[doc = "Bit 4"]
    #[inline(always)]
    pub fn pbus_mem_force_pu(&mut self) -> PBUS_MEM_FORCE_PU_W<'_, MEM_CONF_SPEC> {
        PBUS_MEM_FORCE_PU_W::new(self, 4)
    }
    #[doc = "Bit 5"]
    #[inline(always)]
    pub fn pbus_mem_force_pd(&mut self) -> PBUS_MEM_FORCE_PD_W<'_, MEM_CONF_SPEC> {
        PBUS_MEM_FORCE_PD_W::new(self, 5)
    }
    #[doc = "Bit 6"]
    #[inline(always)]
    pub fn bc_mem_force_pu(&mut self) -> BC_MEM_FORCE_PU_W<'_, MEM_CONF_SPEC> {
        BC_MEM_FORCE_PU_W::new(self, 6)
    }
    #[doc = "Bit 7"]
    #[inline(always)]
    pub fn bc_mem_force_pd(&mut self) -> BC_MEM_FORCE_PD_W<'_, MEM_CONF_SPEC> {
        BC_MEM_FORCE_PD_W::new(self, 7)
    }
    #[doc = "Bit 8"]
    #[inline(always)]
    pub fn i2c_mst_mem_force_pu(&mut self) -> I2C_MST_MEM_FORCE_PU_W<'_, MEM_CONF_SPEC> {
        I2C_MST_MEM_FORCE_PU_W::new(self, 8)
    }
    #[doc = "Bit 9"]
    #[inline(always)]
    pub fn i2c_mst_mem_force_pd(&mut self) -> I2C_MST_MEM_FORCE_PD_W<'_, MEM_CONF_SPEC> {
        I2C_MST_MEM_FORCE_PD_W::new(self, 9)
    }
    #[doc = "Bit 10"]
    #[inline(always)]
    pub fn chan_freq_mem_force_pu(&mut self) -> CHAN_FREQ_MEM_FORCE_PU_W<'_, MEM_CONF_SPEC> {
        CHAN_FREQ_MEM_FORCE_PU_W::new(self, 10)
    }
    #[doc = "Bit 11"]
    #[inline(always)]
    pub fn chan_freq_mem_force_pd(&mut self) -> CHAN_FREQ_MEM_FORCE_PD_W<'_, MEM_CONF_SPEC> {
        CHAN_FREQ_MEM_FORCE_PD_W::new(self, 11)
    }
    #[doc = "Bits 12:14"]
    #[inline(always)]
    pub fn modem_pwr_mem_wp(&mut self) -> MODEM_PWR_MEM_WP_W<'_, MEM_CONF_SPEC> {
        MODEM_PWR_MEM_WP_W::new(self, 12)
    }
    #[doc = "Bits 15:17"]
    #[inline(always)]
    pub fn modem_pwr_mem_wa(&mut self) -> MODEM_PWR_MEM_WA_W<'_, MEM_CONF_SPEC> {
        MODEM_PWR_MEM_WA_W::new(self, 15)
    }
    #[doc = "Bits 18:19"]
    #[inline(always)]
    pub fn modem_pwr_mem_ra(&mut self) -> MODEM_PWR_MEM_RA_W<'_, MEM_CONF_SPEC> {
        MODEM_PWR_MEM_RA_W::new(self, 18)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MEM_CONF_SPEC;
impl crate::RegisterSpec for MEM_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mem_conf::R`](R) reader structure"]
impl crate::Readable for MEM_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mem_conf::W`](W) writer structure"]
impl crate::Writable for MEM_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MEM_CONF to value 0x0002_0015"]
impl crate::Resettable for MEM_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0002_0015;
}
