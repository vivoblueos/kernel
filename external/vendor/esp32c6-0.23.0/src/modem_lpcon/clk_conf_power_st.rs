#[doc = "Register `CLK_CONF_POWER_ST` reader"]
pub type R = crate::R<CLK_CONF_POWER_ST_SPEC>;
#[doc = "Register `CLK_CONF_POWER_ST` writer"]
pub type W = crate::W<CLK_CONF_POWER_ST_SPEC>;
#[doc = "Field `CLK_WIFIPWR_ST_MAP` reader - "]
pub type CLK_WIFIPWR_ST_MAP_R = crate::FieldReader;
#[doc = "Field `CLK_WIFIPWR_ST_MAP` writer - "]
pub type CLK_WIFIPWR_ST_MAP_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CLK_COEX_ST_MAP` reader - "]
pub type CLK_COEX_ST_MAP_R = crate::FieldReader;
#[doc = "Field `CLK_COEX_ST_MAP` writer - "]
pub type CLK_COEX_ST_MAP_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CLK_I2C_MST_ST_MAP` reader - "]
pub type CLK_I2C_MST_ST_MAP_R = crate::FieldReader;
#[doc = "Field `CLK_I2C_MST_ST_MAP` writer - "]
pub type CLK_I2C_MST_ST_MAP_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CLK_LP_APB_ST_MAP` reader - "]
pub type CLK_LP_APB_ST_MAP_R = crate::FieldReader;
#[doc = "Field `CLK_LP_APB_ST_MAP` writer - "]
pub type CLK_LP_APB_ST_MAP_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 16:19"]
    #[inline(always)]
    pub fn clk_wifipwr_st_map(&self) -> CLK_WIFIPWR_ST_MAP_R {
        CLK_WIFIPWR_ST_MAP_R::new(((self.bits >> 16) & 0x0f) as u8)
    }
    #[doc = "Bits 20:23"]
    #[inline(always)]
    pub fn clk_coex_st_map(&self) -> CLK_COEX_ST_MAP_R {
        CLK_COEX_ST_MAP_R::new(((self.bits >> 20) & 0x0f) as u8)
    }
    #[doc = "Bits 24:27"]
    #[inline(always)]
    pub fn clk_i2c_mst_st_map(&self) -> CLK_I2C_MST_ST_MAP_R {
        CLK_I2C_MST_ST_MAP_R::new(((self.bits >> 24) & 0x0f) as u8)
    }
    #[doc = "Bits 28:31"]
    #[inline(always)]
    pub fn clk_lp_apb_st_map(&self) -> CLK_LP_APB_ST_MAP_R {
        CLK_LP_APB_ST_MAP_R::new(((self.bits >> 28) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLK_CONF_POWER_ST")
            .field("clk_wifipwr_st_map", &self.clk_wifipwr_st_map())
            .field("clk_coex_st_map", &self.clk_coex_st_map())
            .field("clk_i2c_mst_st_map", &self.clk_i2c_mst_st_map())
            .field("clk_lp_apb_st_map", &self.clk_lp_apb_st_map())
            .finish()
    }
}
impl W {
    #[doc = "Bits 16:19"]
    #[inline(always)]
    pub fn clk_wifipwr_st_map(&mut self) -> CLK_WIFIPWR_ST_MAP_W<'_, CLK_CONF_POWER_ST_SPEC> {
        CLK_WIFIPWR_ST_MAP_W::new(self, 16)
    }
    #[doc = "Bits 20:23"]
    #[inline(always)]
    pub fn clk_coex_st_map(&mut self) -> CLK_COEX_ST_MAP_W<'_, CLK_CONF_POWER_ST_SPEC> {
        CLK_COEX_ST_MAP_W::new(self, 20)
    }
    #[doc = "Bits 24:27"]
    #[inline(always)]
    pub fn clk_i2c_mst_st_map(&mut self) -> CLK_I2C_MST_ST_MAP_W<'_, CLK_CONF_POWER_ST_SPEC> {
        CLK_I2C_MST_ST_MAP_W::new(self, 24)
    }
    #[doc = "Bits 28:31"]
    #[inline(always)]
    pub fn clk_lp_apb_st_map(&mut self) -> CLK_LP_APB_ST_MAP_W<'_, CLK_CONF_POWER_ST_SPEC> {
        CLK_LP_APB_ST_MAP_W::new(self, 28)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_conf_power_st::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_conf_power_st::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLK_CONF_POWER_ST_SPEC;
impl crate::RegisterSpec for CLK_CONF_POWER_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clk_conf_power_st::R`](R) reader structure"]
impl crate::Readable for CLK_CONF_POWER_ST_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clk_conf_power_st::W`](W) writer structure"]
impl crate::Writable for CLK_CONF_POWER_ST_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLK_CONF_POWER_ST to value 0"]
impl crate::Resettable for CLK_CONF_POWER_ST_SPEC {}
