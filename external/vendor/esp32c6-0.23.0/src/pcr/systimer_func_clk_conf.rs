#[doc = "Register `SYSTIMER_FUNC_CLK_CONF` reader"]
pub type R = crate::R<SYSTIMER_FUNC_CLK_CONF_SPEC>;
#[doc = "Register `SYSTIMER_FUNC_CLK_CONF` writer"]
pub type W = crate::W<SYSTIMER_FUNC_CLK_CONF_SPEC>;
#[doc = "Field `SYSTIMER_FUNC_CLK_SEL` reader - set this field to select clock-source. 0(default): XTAL, 1: FOSC."]
pub type SYSTIMER_FUNC_CLK_SEL_R = crate::BitReader;
#[doc = "Field `SYSTIMER_FUNC_CLK_SEL` writer - set this field to select clock-source. 0(default): XTAL, 1: FOSC."]
pub type SYSTIMER_FUNC_CLK_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SYSTIMER_FUNC_CLK_EN` reader - Set 1 to enable systimer function clock"]
pub type SYSTIMER_FUNC_CLK_EN_R = crate::BitReader;
#[doc = "Field `SYSTIMER_FUNC_CLK_EN` writer - Set 1 to enable systimer function clock"]
pub type SYSTIMER_FUNC_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 20 - set this field to select clock-source. 0(default): XTAL, 1: FOSC."]
    #[inline(always)]
    pub fn systimer_func_clk_sel(&self) -> SYSTIMER_FUNC_CLK_SEL_R {
        SYSTIMER_FUNC_CLK_SEL_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 22 - Set 1 to enable systimer function clock"]
    #[inline(always)]
    pub fn systimer_func_clk_en(&self) -> SYSTIMER_FUNC_CLK_EN_R {
        SYSTIMER_FUNC_CLK_EN_R::new(((self.bits >> 22) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SYSTIMER_FUNC_CLK_CONF")
            .field("systimer_func_clk_sel", &self.systimer_func_clk_sel())
            .field("systimer_func_clk_en", &self.systimer_func_clk_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 20 - set this field to select clock-source. 0(default): XTAL, 1: FOSC."]
    #[inline(always)]
    pub fn systimer_func_clk_sel(
        &mut self,
    ) -> SYSTIMER_FUNC_CLK_SEL_W<'_, SYSTIMER_FUNC_CLK_CONF_SPEC> {
        SYSTIMER_FUNC_CLK_SEL_W::new(self, 20)
    }
    #[doc = "Bit 22 - Set 1 to enable systimer function clock"]
    #[inline(always)]
    pub fn systimer_func_clk_en(
        &mut self,
    ) -> SYSTIMER_FUNC_CLK_EN_W<'_, SYSTIMER_FUNC_CLK_CONF_SPEC> {
        SYSTIMER_FUNC_CLK_EN_W::new(self, 22)
    }
}
#[doc = "SYSTIMER_FUNC_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`systimer_func_clk_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`systimer_func_clk_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SYSTIMER_FUNC_CLK_CONF_SPEC;
impl crate::RegisterSpec for SYSTIMER_FUNC_CLK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`systimer_func_clk_conf::R`](R) reader structure"]
impl crate::Readable for SYSTIMER_FUNC_CLK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`systimer_func_clk_conf::W`](W) writer structure"]
impl crate::Writable for SYSTIMER_FUNC_CLK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SYSTIMER_FUNC_CLK_CONF to value 0x0040_0000"]
impl crate::Resettable for SYSTIMER_FUNC_CLK_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0040_0000;
}
