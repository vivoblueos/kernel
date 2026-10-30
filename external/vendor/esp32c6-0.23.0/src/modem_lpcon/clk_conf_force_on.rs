#[doc = "Register `CLK_CONF_FORCE_ON` reader"]
pub type R = crate::R<CLK_CONF_FORCE_ON_SPEC>;
#[doc = "Register `CLK_CONF_FORCE_ON` writer"]
pub type W = crate::W<CLK_CONF_FORCE_ON_SPEC>;
#[doc = "Field `CLK_WIFIPWR_FO` reader - "]
pub type CLK_WIFIPWR_FO_R = crate::BitReader;
#[doc = "Field `CLK_WIFIPWR_FO` writer - "]
pub type CLK_WIFIPWR_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_COEX_FO` reader - "]
pub type CLK_COEX_FO_R = crate::BitReader;
#[doc = "Field `CLK_COEX_FO` writer - "]
pub type CLK_COEX_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_I2C_MST_FO` reader - "]
pub type CLK_I2C_MST_FO_R = crate::BitReader;
#[doc = "Field `CLK_I2C_MST_FO` writer - "]
pub type CLK_I2C_MST_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_LP_TIMER_FO` reader - "]
pub type CLK_LP_TIMER_FO_R = crate::BitReader;
#[doc = "Field `CLK_LP_TIMER_FO` writer - "]
pub type CLK_LP_TIMER_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_BCMEM_FO` reader - "]
pub type CLK_BCMEM_FO_R = crate::BitReader;
#[doc = "Field `CLK_BCMEM_FO` writer - "]
pub type CLK_BCMEM_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_I2C_MST_MEM_FO` reader - "]
pub type CLK_I2C_MST_MEM_FO_R = crate::BitReader;
#[doc = "Field `CLK_I2C_MST_MEM_FO` writer - "]
pub type CLK_I2C_MST_MEM_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_CHAN_FREQ_MEM_FO` reader - "]
pub type CLK_CHAN_FREQ_MEM_FO_R = crate::BitReader;
#[doc = "Field `CLK_CHAN_FREQ_MEM_FO` writer - "]
pub type CLK_CHAN_FREQ_MEM_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_PBUS_MEM_FO` reader - "]
pub type CLK_PBUS_MEM_FO_R = crate::BitReader;
#[doc = "Field `CLK_PBUS_MEM_FO` writer - "]
pub type CLK_PBUS_MEM_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_AGC_MEM_FO` reader - "]
pub type CLK_AGC_MEM_FO_R = crate::BitReader;
#[doc = "Field `CLK_AGC_MEM_FO` writer - "]
pub type CLK_AGC_MEM_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_DC_MEM_FO` reader - "]
pub type CLK_DC_MEM_FO_R = crate::BitReader;
#[doc = "Field `CLK_DC_MEM_FO` writer - "]
pub type CLK_DC_MEM_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn clk_wifipwr_fo(&self) -> CLK_WIFIPWR_FO_R {
        CLK_WIFIPWR_FO_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn clk_coex_fo(&self) -> CLK_COEX_FO_R {
        CLK_COEX_FO_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2"]
    #[inline(always)]
    pub fn clk_i2c_mst_fo(&self) -> CLK_I2C_MST_FO_R {
        CLK_I2C_MST_FO_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn clk_lp_timer_fo(&self) -> CLK_LP_TIMER_FO_R {
        CLK_LP_TIMER_FO_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4"]
    #[inline(always)]
    pub fn clk_bcmem_fo(&self) -> CLK_BCMEM_FO_R {
        CLK_BCMEM_FO_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5"]
    #[inline(always)]
    pub fn clk_i2c_mst_mem_fo(&self) -> CLK_I2C_MST_MEM_FO_R {
        CLK_I2C_MST_MEM_FO_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6"]
    #[inline(always)]
    pub fn clk_chan_freq_mem_fo(&self) -> CLK_CHAN_FREQ_MEM_FO_R {
        CLK_CHAN_FREQ_MEM_FO_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7"]
    #[inline(always)]
    pub fn clk_pbus_mem_fo(&self) -> CLK_PBUS_MEM_FO_R {
        CLK_PBUS_MEM_FO_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8"]
    #[inline(always)]
    pub fn clk_agc_mem_fo(&self) -> CLK_AGC_MEM_FO_R {
        CLK_AGC_MEM_FO_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9"]
    #[inline(always)]
    pub fn clk_dc_mem_fo(&self) -> CLK_DC_MEM_FO_R {
        CLK_DC_MEM_FO_R::new(((self.bits >> 9) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLK_CONF_FORCE_ON")
            .field("clk_wifipwr_fo", &self.clk_wifipwr_fo())
            .field("clk_coex_fo", &self.clk_coex_fo())
            .field("clk_i2c_mst_fo", &self.clk_i2c_mst_fo())
            .field("clk_lp_timer_fo", &self.clk_lp_timer_fo())
            .field("clk_bcmem_fo", &self.clk_bcmem_fo())
            .field("clk_i2c_mst_mem_fo", &self.clk_i2c_mst_mem_fo())
            .field("clk_chan_freq_mem_fo", &self.clk_chan_freq_mem_fo())
            .field("clk_pbus_mem_fo", &self.clk_pbus_mem_fo())
            .field("clk_agc_mem_fo", &self.clk_agc_mem_fo())
            .field("clk_dc_mem_fo", &self.clk_dc_mem_fo())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn clk_wifipwr_fo(&mut self) -> CLK_WIFIPWR_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_WIFIPWR_FO_W::new(self, 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn clk_coex_fo(&mut self) -> CLK_COEX_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_COEX_FO_W::new(self, 1)
    }
    #[doc = "Bit 2"]
    #[inline(always)]
    pub fn clk_i2c_mst_fo(&mut self) -> CLK_I2C_MST_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_I2C_MST_FO_W::new(self, 2)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn clk_lp_timer_fo(&mut self) -> CLK_LP_TIMER_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_LP_TIMER_FO_W::new(self, 3)
    }
    #[doc = "Bit 4"]
    #[inline(always)]
    pub fn clk_bcmem_fo(&mut self) -> CLK_BCMEM_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_BCMEM_FO_W::new(self, 4)
    }
    #[doc = "Bit 5"]
    #[inline(always)]
    pub fn clk_i2c_mst_mem_fo(&mut self) -> CLK_I2C_MST_MEM_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_I2C_MST_MEM_FO_W::new(self, 5)
    }
    #[doc = "Bit 6"]
    #[inline(always)]
    pub fn clk_chan_freq_mem_fo(&mut self) -> CLK_CHAN_FREQ_MEM_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_CHAN_FREQ_MEM_FO_W::new(self, 6)
    }
    #[doc = "Bit 7"]
    #[inline(always)]
    pub fn clk_pbus_mem_fo(&mut self) -> CLK_PBUS_MEM_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_PBUS_MEM_FO_W::new(self, 7)
    }
    #[doc = "Bit 8"]
    #[inline(always)]
    pub fn clk_agc_mem_fo(&mut self) -> CLK_AGC_MEM_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_AGC_MEM_FO_W::new(self, 8)
    }
    #[doc = "Bit 9"]
    #[inline(always)]
    pub fn clk_dc_mem_fo(&mut self) -> CLK_DC_MEM_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_DC_MEM_FO_W::new(self, 9)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_conf_force_on::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_conf_force_on::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLK_CONF_FORCE_ON_SPEC;
impl crate::RegisterSpec for CLK_CONF_FORCE_ON_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clk_conf_force_on::R`](R) reader structure"]
impl crate::Readable for CLK_CONF_FORCE_ON_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clk_conf_force_on::W`](W) writer structure"]
impl crate::Writable for CLK_CONF_FORCE_ON_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLK_CONF_FORCE_ON to value 0"]
impl crate::Resettable for CLK_CONF_FORCE_ON_SPEC {}
