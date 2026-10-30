#[doc = "Register `RST_CONF` writer"]
pub type W = crate::W<RST_CONF_SPEC>;
#[doc = "Field `RST_WIFIPWR` writer - "]
pub type RST_WIFIPWR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_COEX` writer - "]
pub type RST_COEX_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_I2C_MST` writer - "]
pub type RST_I2C_MST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_LP_TIMER` writer - "]
pub type RST_LP_TIMER_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<RST_CONF_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn rst_wifipwr(&mut self) -> RST_WIFIPWR_W<'_, RST_CONF_SPEC> {
        RST_WIFIPWR_W::new(self, 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn rst_coex(&mut self) -> RST_COEX_W<'_, RST_CONF_SPEC> {
        RST_COEX_W::new(self, 1)
    }
    #[doc = "Bit 2"]
    #[inline(always)]
    pub fn rst_i2c_mst(&mut self) -> RST_I2C_MST_W<'_, RST_CONF_SPEC> {
        RST_I2C_MST_W::new(self, 2)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn rst_lp_timer(&mut self) -> RST_LP_TIMER_W<'_, RST_CONF_SPEC> {
        RST_LP_TIMER_W::new(self, 3)
    }
}
#[doc = "\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rst_conf::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RST_CONF_SPEC;
impl crate::RegisterSpec for RST_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`rst_conf::W`](W) writer structure"]
impl crate::Writable for RST_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RST_CONF to value 0"]
impl crate::Resettable for RST_CONF_SPEC {}
