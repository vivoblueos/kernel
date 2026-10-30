#[doc = "Register `ETM_CONF` reader"]
pub type R = crate::R<ETM_CONF_SPEC>;
#[doc = "Register `ETM_CONF` writer"]
pub type W = crate::W<ETM_CONF_SPEC>;
#[doc = "Field `ETM_CLK_EN` reader - Set 1 to enable etm clock"]
pub type ETM_CLK_EN_R = crate::BitReader;
#[doc = "Field `ETM_CLK_EN` writer - Set 1 to enable etm clock"]
pub type ETM_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ETM_RST_EN` reader - Set 0 to reset etm module"]
pub type ETM_RST_EN_R = crate::BitReader;
#[doc = "Field `ETM_RST_EN` writer - Set 0 to reset etm module"]
pub type ETM_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable etm clock"]
    #[inline(always)]
    pub fn etm_clk_en(&self) -> ETM_CLK_EN_R {
        ETM_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset etm module"]
    #[inline(always)]
    pub fn etm_rst_en(&self) -> ETM_RST_EN_R {
        ETM_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ETM_CONF")
            .field("etm_clk_en", &self.etm_clk_en())
            .field("etm_rst_en", &self.etm_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable etm clock"]
    #[inline(always)]
    pub fn etm_clk_en(&mut self) -> ETM_CLK_EN_W<'_, ETM_CONF_SPEC> {
        ETM_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset etm module"]
    #[inline(always)]
    pub fn etm_rst_en(&mut self) -> ETM_RST_EN_W<'_, ETM_CONF_SPEC> {
        ETM_RST_EN_W::new(self, 1)
    }
}
#[doc = "ETM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`etm_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`etm_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ETM_CONF_SPEC;
impl crate::RegisterSpec for ETM_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`etm_conf::R`](R) reader structure"]
impl crate::Readable for ETM_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`etm_conf::W`](W) writer structure"]
impl crate::Writable for ETM_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ETM_CONF to value 0x01"]
impl crate::Resettable for ETM_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
