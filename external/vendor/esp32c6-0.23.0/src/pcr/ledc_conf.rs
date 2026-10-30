#[doc = "Register `LEDC_CONF` reader"]
pub type R = crate::R<LEDC_CONF_SPEC>;
#[doc = "Register `LEDC_CONF` writer"]
pub type W = crate::W<LEDC_CONF_SPEC>;
#[doc = "Field `LEDC_CLK_EN` reader - Set 1 to enable ledc apb clock"]
pub type LEDC_CLK_EN_R = crate::BitReader;
#[doc = "Field `LEDC_CLK_EN` writer - Set 1 to enable ledc apb clock"]
pub type LEDC_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LEDC_RST_EN` reader - Set 0 to reset ledc module"]
pub type LEDC_RST_EN_R = crate::BitReader;
#[doc = "Field `LEDC_RST_EN` writer - Set 0 to reset ledc module"]
pub type LEDC_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable ledc apb clock"]
    #[inline(always)]
    pub fn ledc_clk_en(&self) -> LEDC_CLK_EN_R {
        LEDC_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset ledc module"]
    #[inline(always)]
    pub fn ledc_rst_en(&self) -> LEDC_RST_EN_R {
        LEDC_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LEDC_CONF")
            .field("ledc_clk_en", &self.ledc_clk_en())
            .field("ledc_rst_en", &self.ledc_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable ledc apb clock"]
    #[inline(always)]
    pub fn ledc_clk_en(&mut self) -> LEDC_CLK_EN_W<'_, LEDC_CONF_SPEC> {
        LEDC_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset ledc module"]
    #[inline(always)]
    pub fn ledc_rst_en(&mut self) -> LEDC_RST_EN_W<'_, LEDC_CONF_SPEC> {
        LEDC_RST_EN_W::new(self, 1)
    }
}
#[doc = "LEDC configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ledc_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ledc_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LEDC_CONF_SPEC;
impl crate::RegisterSpec for LEDC_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ledc_conf::R`](R) reader structure"]
impl crate::Readable for LEDC_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ledc_conf::W`](W) writer structure"]
impl crate::Writable for LEDC_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LEDC_CONF to value 0x01"]
impl crate::Resettable for LEDC_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
