#[doc = "Register `MSPI_CONF` reader"]
pub type R = crate::R<MSPI_CONF_SPEC>;
#[doc = "Register `MSPI_CONF` writer"]
pub type W = crate::W<MSPI_CONF_SPEC>;
#[doc = "Field `MSPI_CLK_EN` reader - Set 1 to enable mspi clock, include mspi pll clock"]
pub type MSPI_CLK_EN_R = crate::BitReader;
#[doc = "Field `MSPI_CLK_EN` writer - Set 1 to enable mspi clock, include mspi pll clock"]
pub type MSPI_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MSPI_RST_EN` reader - Set 0 to reset mspi module"]
pub type MSPI_RST_EN_R = crate::BitReader;
#[doc = "Field `MSPI_RST_EN` writer - Set 0 to reset mspi module"]
pub type MSPI_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MSPI_PLL_CLK_EN` reader - Set 1 to enable mspi pll clock"]
pub type MSPI_PLL_CLK_EN_R = crate::BitReader;
#[doc = "Field `MSPI_PLL_CLK_EN` writer - Set 1 to enable mspi pll clock"]
pub type MSPI_PLL_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable mspi clock, include mspi pll clock"]
    #[inline(always)]
    pub fn mspi_clk_en(&self) -> MSPI_CLK_EN_R {
        MSPI_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset mspi module"]
    #[inline(always)]
    pub fn mspi_rst_en(&self) -> MSPI_RST_EN_R {
        MSPI_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set 1 to enable mspi pll clock"]
    #[inline(always)]
    pub fn mspi_pll_clk_en(&self) -> MSPI_PLL_CLK_EN_R {
        MSPI_PLL_CLK_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MSPI_CONF")
            .field("mspi_clk_en", &self.mspi_clk_en())
            .field("mspi_rst_en", &self.mspi_rst_en())
            .field("mspi_pll_clk_en", &self.mspi_pll_clk_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable mspi clock, include mspi pll clock"]
    #[inline(always)]
    pub fn mspi_clk_en(&mut self) -> MSPI_CLK_EN_W<'_, MSPI_CONF_SPEC> {
        MSPI_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset mspi module"]
    #[inline(always)]
    pub fn mspi_rst_en(&mut self) -> MSPI_RST_EN_W<'_, MSPI_CONF_SPEC> {
        MSPI_RST_EN_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set 1 to enable mspi pll clock"]
    #[inline(always)]
    pub fn mspi_pll_clk_en(&mut self) -> MSPI_PLL_CLK_EN_W<'_, MSPI_CONF_SPEC> {
        MSPI_PLL_CLK_EN_W::new(self, 2)
    }
}
#[doc = "MSPI configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`mspi_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mspi_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MSPI_CONF_SPEC;
impl crate::RegisterSpec for MSPI_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mspi_conf::R`](R) reader structure"]
impl crate::Readable for MSPI_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mspi_conf::W`](W) writer structure"]
impl crate::Writable for MSPI_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MSPI_CONF to value 0x05"]
impl crate::Resettable for MSPI_CONF_SPEC {
    const RESET_VALUE: u32 = 0x05;
}
