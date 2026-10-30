#[doc = "Register `I2C_MST_CLK_CONF` reader"]
pub type R = crate::R<I2C_MST_CLK_CONF_SPEC>;
#[doc = "Register `I2C_MST_CLK_CONF` writer"]
pub type W = crate::W<I2C_MST_CLK_CONF_SPEC>;
#[doc = "Field `CLK_I2C_MST_SEL_160M` reader - "]
pub type CLK_I2C_MST_SEL_160M_R = crate::BitReader;
#[doc = "Field `CLK_I2C_MST_SEL_160M` writer - "]
pub type CLK_I2C_MST_SEL_160M_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn clk_i2c_mst_sel_160m(&self) -> CLK_I2C_MST_SEL_160M_R {
        CLK_I2C_MST_SEL_160M_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("I2C_MST_CLK_CONF")
            .field("clk_i2c_mst_sel_160m", &self.clk_i2c_mst_sel_160m())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn clk_i2c_mst_sel_160m(&mut self) -> CLK_I2C_MST_SEL_160M_W<'_, I2C_MST_CLK_CONF_SPEC> {
        CLK_I2C_MST_SEL_160M_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c_mst_clk_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c_mst_clk_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct I2C_MST_CLK_CONF_SPEC;
impl crate::RegisterSpec for I2C_MST_CLK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`i2c_mst_clk_conf::R`](R) reader structure"]
impl crate::Readable for I2C_MST_CLK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`i2c_mst_clk_conf::W`](W) writer structure"]
impl crate::Writable for I2C_MST_CLK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets I2C_MST_CLK_CONF to value 0"]
impl crate::Resettable for I2C_MST_CLK_CONF_SPEC {}
