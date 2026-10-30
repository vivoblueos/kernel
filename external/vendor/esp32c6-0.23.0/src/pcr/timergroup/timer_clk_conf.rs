#[doc = "Register `TIMER_CLK_CONF` reader"]
pub type R = crate::R<TIMER_CLK_CONF_SPEC>;
#[doc = "Register `TIMER_CLK_CONF` writer"]
pub type W = crate::W<TIMER_CLK_CONF_SPEC>;
#[doc = "Field `TIMER_CLK_SEL` reader - set this field to select clock-source. 0(default): XTAL, 1: 80MHz, 2: FOSC, 3: reserved."]
pub type TIMER_CLK_SEL_R = crate::FieldReader;
#[doc = "Field `TIMER_CLK_SEL` writer - set this field to select clock-source. 0(default): XTAL, 1: 80MHz, 2: FOSC, 3: reserved."]
pub type TIMER_CLK_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `TIMER_CLK_EN` reader - Set 1 to enable timer_group0 timer clock"]
pub type TIMER_CLK_EN_R = crate::BitReader;
#[doc = "Field `TIMER_CLK_EN` writer - Set 1 to enable timer_group0 timer clock"]
pub type TIMER_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 20:21 - set this field to select clock-source. 0(default): XTAL, 1: 80MHz, 2: FOSC, 3: reserved."]
    #[inline(always)]
    pub fn timer_clk_sel(&self) -> TIMER_CLK_SEL_R {
        TIMER_CLK_SEL_R::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bit 22 - Set 1 to enable timer_group0 timer clock"]
    #[inline(always)]
    pub fn timer_clk_en(&self) -> TIMER_CLK_EN_R {
        TIMER_CLK_EN_R::new(((self.bits >> 22) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TIMER_CLK_CONF")
            .field("timer_clk_sel", &self.timer_clk_sel())
            .field("timer_clk_en", &self.timer_clk_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 20:21 - set this field to select clock-source. 0(default): XTAL, 1: 80MHz, 2: FOSC, 3: reserved."]
    #[inline(always)]
    pub fn timer_clk_sel(&mut self) -> TIMER_CLK_SEL_W<'_, TIMER_CLK_CONF_SPEC> {
        TIMER_CLK_SEL_W::new(self, 20)
    }
    #[doc = "Bit 22 - Set 1 to enable timer_group0 timer clock"]
    #[inline(always)]
    pub fn timer_clk_en(&mut self) -> TIMER_CLK_EN_W<'_, TIMER_CLK_CONF_SPEC> {
        TIMER_CLK_EN_W::new(self, 22)
    }
}
#[doc = "TIMERGROUP0_TIMER_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`timer_clk_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`timer_clk_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TIMER_CLK_CONF_SPEC;
impl crate::RegisterSpec for TIMER_CLK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`timer_clk_conf::R`](R) reader structure"]
impl crate::Readable for TIMER_CLK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`timer_clk_conf::W`](W) writer structure"]
impl crate::Writable for TIMER_CLK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TIMER_CLK_CONF to value 0x0040_0000"]
impl crate::Resettable for TIMER_CLK_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0040_0000;
}
