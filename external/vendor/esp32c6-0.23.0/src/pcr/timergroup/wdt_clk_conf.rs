#[doc = "Register `WDT_CLK_CONF` reader"]
pub type R = crate::R<WDT_CLK_CONF_SPEC>;
#[doc = "Register `WDT_CLK_CONF` writer"]
pub type W = crate::W<WDT_CLK_CONF_SPEC>;
#[doc = "Field `WDT_CLK_SEL` reader - set this field to select clock-source. 0(default): XTAL, 1: 80MHz, 2: FOSC, 3: reserved."]
pub type WDT_CLK_SEL_R = crate::FieldReader;
#[doc = "Field `WDT_CLK_SEL` writer - set this field to select clock-source. 0(default): XTAL, 1: 80MHz, 2: FOSC, 3: reserved."]
pub type WDT_CLK_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `WDT_CLK_EN` reader - Set 1 to enable timer_group0 wdt clock"]
pub type WDT_CLK_EN_R = crate::BitReader;
#[doc = "Field `WDT_CLK_EN` writer - Set 1 to enable timer_group0 wdt clock"]
pub type WDT_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 20:21 - set this field to select clock-source. 0(default): XTAL, 1: 80MHz, 2: FOSC, 3: reserved."]
    #[inline(always)]
    pub fn wdt_clk_sel(&self) -> WDT_CLK_SEL_R {
        WDT_CLK_SEL_R::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bit 22 - Set 1 to enable timer_group0 wdt clock"]
    #[inline(always)]
    pub fn wdt_clk_en(&self) -> WDT_CLK_EN_R {
        WDT_CLK_EN_R::new(((self.bits >> 22) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("WDT_CLK_CONF")
            .field("wdt_clk_sel", &self.wdt_clk_sel())
            .field("wdt_clk_en", &self.wdt_clk_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 20:21 - set this field to select clock-source. 0(default): XTAL, 1: 80MHz, 2: FOSC, 3: reserved."]
    #[inline(always)]
    pub fn wdt_clk_sel(&mut self) -> WDT_CLK_SEL_W<'_, WDT_CLK_CONF_SPEC> {
        WDT_CLK_SEL_W::new(self, 20)
    }
    #[doc = "Bit 22 - Set 1 to enable timer_group0 wdt clock"]
    #[inline(always)]
    pub fn wdt_clk_en(&mut self) -> WDT_CLK_EN_W<'_, WDT_CLK_CONF_SPEC> {
        WDT_CLK_EN_W::new(self, 22)
    }
}
#[doc = "TIMERGROUP0_WDT_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`wdt_clk_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wdt_clk_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct WDT_CLK_CONF_SPEC;
impl crate::RegisterSpec for WDT_CLK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`wdt_clk_conf::R`](R) reader structure"]
impl crate::Readable for WDT_CLK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`wdt_clk_conf::W`](W) writer structure"]
impl crate::Writable for WDT_CLK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets WDT_CLK_CONF to value 0x0040_0000"]
impl crate::Resettable for WDT_CLK_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0040_0000;
}
