#[doc = "Register `CLK_CONF` reader"]
pub type R = crate::R<CLK_CONF_SPEC>;
#[doc = "Register `CLK_CONF` writer"]
pub type W = crate::W<CLK_CONF_SPEC>;
#[doc = "Field `CLK_WIFIPWR_EN` reader - "]
pub type CLK_WIFIPWR_EN_R = crate::BitReader;
#[doc = "Field `CLK_WIFIPWR_EN` writer - "]
pub type CLK_WIFIPWR_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_COEX_EN` reader - "]
pub type CLK_COEX_EN_R = crate::BitReader;
#[doc = "Field `CLK_COEX_EN` writer - "]
pub type CLK_COEX_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_I2C_MST_EN` reader - "]
pub type CLK_I2C_MST_EN_R = crate::BitReader;
#[doc = "Field `CLK_I2C_MST_EN` writer - "]
pub type CLK_I2C_MST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_LP_TIMER_EN` reader - "]
pub type CLK_LP_TIMER_EN_R = crate::BitReader;
#[doc = "Field `CLK_LP_TIMER_EN` writer - "]
pub type CLK_LP_TIMER_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn clk_wifipwr_en(&self) -> CLK_WIFIPWR_EN_R {
        CLK_WIFIPWR_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn clk_coex_en(&self) -> CLK_COEX_EN_R {
        CLK_COEX_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2"]
    #[inline(always)]
    pub fn clk_i2c_mst_en(&self) -> CLK_I2C_MST_EN_R {
        CLK_I2C_MST_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn clk_lp_timer_en(&self) -> CLK_LP_TIMER_EN_R {
        CLK_LP_TIMER_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLK_CONF")
            .field("clk_wifipwr_en", &self.clk_wifipwr_en())
            .field("clk_coex_en", &self.clk_coex_en())
            .field("clk_i2c_mst_en", &self.clk_i2c_mst_en())
            .field("clk_lp_timer_en", &self.clk_lp_timer_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn clk_wifipwr_en(&mut self) -> CLK_WIFIPWR_EN_W<'_, CLK_CONF_SPEC> {
        CLK_WIFIPWR_EN_W::new(self, 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn clk_coex_en(&mut self) -> CLK_COEX_EN_W<'_, CLK_CONF_SPEC> {
        CLK_COEX_EN_W::new(self, 1)
    }
    #[doc = "Bit 2"]
    #[inline(always)]
    pub fn clk_i2c_mst_en(&mut self) -> CLK_I2C_MST_EN_W<'_, CLK_CONF_SPEC> {
        CLK_I2C_MST_EN_W::new(self, 2)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn clk_lp_timer_en(&mut self) -> CLK_LP_TIMER_EN_W<'_, CLK_CONF_SPEC> {
        CLK_LP_TIMER_EN_W::new(self, 3)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLK_CONF_SPEC;
impl crate::RegisterSpec for CLK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clk_conf::R`](R) reader structure"]
impl crate::Readable for CLK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clk_conf::W`](W) writer structure"]
impl crate::Writable for CLK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLK_CONF to value 0"]
impl crate::Resettable for CLK_CONF_SPEC {}
