#[doc = "Register `LP_TIMER_CONF` reader"]
pub type R = crate::R<LP_TIMER_CONF_SPEC>;
#[doc = "Register `LP_TIMER_CONF` writer"]
pub type W = crate::W<LP_TIMER_CONF_SPEC>;
#[doc = "Field `CLK_LP_TIMER_SEL_OSC_SLOW` reader - "]
pub type CLK_LP_TIMER_SEL_OSC_SLOW_R = crate::BitReader;
#[doc = "Field `CLK_LP_TIMER_SEL_OSC_SLOW` writer - "]
pub type CLK_LP_TIMER_SEL_OSC_SLOW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_LP_TIMER_SEL_OSC_FAST` reader - "]
pub type CLK_LP_TIMER_SEL_OSC_FAST_R = crate::BitReader;
#[doc = "Field `CLK_LP_TIMER_SEL_OSC_FAST` writer - "]
pub type CLK_LP_TIMER_SEL_OSC_FAST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_LP_TIMER_SEL_XTAL` reader - "]
pub type CLK_LP_TIMER_SEL_XTAL_R = crate::BitReader;
#[doc = "Field `CLK_LP_TIMER_SEL_XTAL` writer - "]
pub type CLK_LP_TIMER_SEL_XTAL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_LP_TIMER_SEL_XTAL32K` reader - "]
pub type CLK_LP_TIMER_SEL_XTAL32K_R = crate::BitReader;
#[doc = "Field `CLK_LP_TIMER_SEL_XTAL32K` writer - "]
pub type CLK_LP_TIMER_SEL_XTAL32K_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_LP_TIMER_DIV_NUM` reader - "]
pub type CLK_LP_TIMER_DIV_NUM_R = crate::FieldReader<u16>;
#[doc = "Field `CLK_LP_TIMER_DIV_NUM` writer - "]
pub type CLK_LP_TIMER_DIV_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
impl R {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn clk_lp_timer_sel_osc_slow(&self) -> CLK_LP_TIMER_SEL_OSC_SLOW_R {
        CLK_LP_TIMER_SEL_OSC_SLOW_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn clk_lp_timer_sel_osc_fast(&self) -> CLK_LP_TIMER_SEL_OSC_FAST_R {
        CLK_LP_TIMER_SEL_OSC_FAST_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2"]
    #[inline(always)]
    pub fn clk_lp_timer_sel_xtal(&self) -> CLK_LP_TIMER_SEL_XTAL_R {
        CLK_LP_TIMER_SEL_XTAL_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn clk_lp_timer_sel_xtal32k(&self) -> CLK_LP_TIMER_SEL_XTAL32K_R {
        CLK_LP_TIMER_SEL_XTAL32K_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:15"]
    #[inline(always)]
    pub fn clk_lp_timer_div_num(&self) -> CLK_LP_TIMER_DIV_NUM_R {
        CLK_LP_TIMER_DIV_NUM_R::new(((self.bits >> 4) & 0x0fff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LP_TIMER_CONF")
            .field(
                "clk_lp_timer_sel_osc_slow",
                &self.clk_lp_timer_sel_osc_slow(),
            )
            .field(
                "clk_lp_timer_sel_osc_fast",
                &self.clk_lp_timer_sel_osc_fast(),
            )
            .field("clk_lp_timer_sel_xtal", &self.clk_lp_timer_sel_xtal())
            .field("clk_lp_timer_sel_xtal32k", &self.clk_lp_timer_sel_xtal32k())
            .field("clk_lp_timer_div_num", &self.clk_lp_timer_div_num())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn clk_lp_timer_sel_osc_slow(
        &mut self,
    ) -> CLK_LP_TIMER_SEL_OSC_SLOW_W<'_, LP_TIMER_CONF_SPEC> {
        CLK_LP_TIMER_SEL_OSC_SLOW_W::new(self, 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn clk_lp_timer_sel_osc_fast(
        &mut self,
    ) -> CLK_LP_TIMER_SEL_OSC_FAST_W<'_, LP_TIMER_CONF_SPEC> {
        CLK_LP_TIMER_SEL_OSC_FAST_W::new(self, 1)
    }
    #[doc = "Bit 2"]
    #[inline(always)]
    pub fn clk_lp_timer_sel_xtal(&mut self) -> CLK_LP_TIMER_SEL_XTAL_W<'_, LP_TIMER_CONF_SPEC> {
        CLK_LP_TIMER_SEL_XTAL_W::new(self, 2)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn clk_lp_timer_sel_xtal32k(
        &mut self,
    ) -> CLK_LP_TIMER_SEL_XTAL32K_W<'_, LP_TIMER_CONF_SPEC> {
        CLK_LP_TIMER_SEL_XTAL32K_W::new(self, 3)
    }
    #[doc = "Bits 4:15"]
    #[inline(always)]
    pub fn clk_lp_timer_div_num(&mut self) -> CLK_LP_TIMER_DIV_NUM_W<'_, LP_TIMER_CONF_SPEC> {
        CLK_LP_TIMER_DIV_NUM_W::new(self, 4)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`lp_timer_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lp_timer_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LP_TIMER_CONF_SPEC;
impl crate::RegisterSpec for LP_TIMER_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lp_timer_conf::R`](R) reader structure"]
impl crate::Readable for LP_TIMER_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`lp_timer_conf::W`](W) writer structure"]
impl crate::Writable for LP_TIMER_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LP_TIMER_CONF to value 0"]
impl crate::Resettable for LP_TIMER_CONF_SPEC {}
