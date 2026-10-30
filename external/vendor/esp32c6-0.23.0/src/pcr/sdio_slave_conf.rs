#[doc = "Register `SDIO_SLAVE_CONF` reader"]
pub type R = crate::R<SDIO_SLAVE_CONF_SPEC>;
#[doc = "Register `SDIO_SLAVE_CONF` writer"]
pub type W = crate::W<SDIO_SLAVE_CONF_SPEC>;
#[doc = "Field `SDIO_SLAVE_CLK_EN` reader - Set 1 to enable sdio_slave clock"]
pub type SDIO_SLAVE_CLK_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLAVE_CLK_EN` writer - Set 1 to enable sdio_slave clock"]
pub type SDIO_SLAVE_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLAVE_RST_EN` reader - Set 0 to reset sdio_slave module"]
pub type SDIO_SLAVE_RST_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLAVE_RST_EN` writer - Set 0 to reset sdio_slave module"]
pub type SDIO_SLAVE_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable sdio_slave clock"]
    #[inline(always)]
    pub fn sdio_slave_clk_en(&self) -> SDIO_SLAVE_CLK_EN_R {
        SDIO_SLAVE_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset sdio_slave module"]
    #[inline(always)]
    pub fn sdio_slave_rst_en(&self) -> SDIO_SLAVE_RST_EN_R {
        SDIO_SLAVE_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SDIO_SLAVE_CONF")
            .field("sdio_slave_clk_en", &self.sdio_slave_clk_en())
            .field("sdio_slave_rst_en", &self.sdio_slave_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable sdio_slave clock"]
    #[inline(always)]
    pub fn sdio_slave_clk_en(&mut self) -> SDIO_SLAVE_CLK_EN_W<'_, SDIO_SLAVE_CONF_SPEC> {
        SDIO_SLAVE_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset sdio_slave module"]
    #[inline(always)]
    pub fn sdio_slave_rst_en(&mut self) -> SDIO_SLAVE_RST_EN_W<'_, SDIO_SLAVE_CONF_SPEC> {
        SDIO_SLAVE_RST_EN_W::new(self, 1)
    }
}
#[doc = "SDIO_SLAVE configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sdio_slave_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sdio_slave_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SDIO_SLAVE_CONF_SPEC;
impl crate::RegisterSpec for SDIO_SLAVE_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sdio_slave_conf::R`](R) reader structure"]
impl crate::Readable for SDIO_SLAVE_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sdio_slave_conf::W`](W) writer structure"]
impl crate::Writable for SDIO_SLAVE_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SDIO_SLAVE_CONF to value 0x01"]
impl crate::Resettable for SDIO_SLAVE_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
