#[doc = "Register `SLOW_CLK_CONF` reader"]
pub type R = crate::R<SLOW_CLK_CONF_SPEC>;
#[doc = "Register `SLOW_CLK_CONF` writer"]
pub type W = crate::W<SLOW_CLK_CONF_SPEC>;
#[doc = "Field `ANA_CLK_DIV_VLD` reader - used to sync div bus. clear vld before set reg_rtc_ana_clk_div"]
pub type ANA_CLK_DIV_VLD_R = crate::BitReader;
#[doc = "Field `ANA_CLK_DIV_VLD` writer - used to sync div bus. clear vld before set reg_rtc_ana_clk_div"]
pub type ANA_CLK_DIV_VLD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ANA_CLK_DIV` reader - the clk divider num of RTC_CLK"]
pub type ANA_CLK_DIV_R = crate::FieldReader;
#[doc = "Field `ANA_CLK_DIV` writer - the clk divider num of RTC_CLK"]
pub type ANA_CLK_DIV_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLOW_CLK_NEXT_EDGE` reader - flag rtc_slow_clk_next_edge"]
pub type SLOW_CLK_NEXT_EDGE_R = crate::BitReader;
#[doc = "Field `SLOW_CLK_NEXT_EDGE` writer - flag rtc_slow_clk_next_edge"]
pub type SLOW_CLK_NEXT_EDGE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 22 - used to sync div bus. clear vld before set reg_rtc_ana_clk_div"]
    #[inline(always)]
    pub fn ana_clk_div_vld(&self) -> ANA_CLK_DIV_VLD_R {
        ANA_CLK_DIV_VLD_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bits 23:30 - the clk divider num of RTC_CLK"]
    #[inline(always)]
    pub fn ana_clk_div(&self) -> ANA_CLK_DIV_R {
        ANA_CLK_DIV_R::new(((self.bits >> 23) & 0xff) as u8)
    }
    #[doc = "Bit 31 - flag rtc_slow_clk_next_edge"]
    #[inline(always)]
    pub fn slow_clk_next_edge(&self) -> SLOW_CLK_NEXT_EDGE_R {
        SLOW_CLK_NEXT_EDGE_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLOW_CLK_CONF")
            .field("ana_clk_div_vld", &self.ana_clk_div_vld())
            .field("ana_clk_div", &self.ana_clk_div())
            .field("slow_clk_next_edge", &self.slow_clk_next_edge())
            .finish()
    }
}
impl W {
    #[doc = "Bit 22 - used to sync div bus. clear vld before set reg_rtc_ana_clk_div"]
    #[inline(always)]
    pub fn ana_clk_div_vld(&mut self) -> ANA_CLK_DIV_VLD_W<'_, SLOW_CLK_CONF_SPEC> {
        ANA_CLK_DIV_VLD_W::new(self, 22)
    }
    #[doc = "Bits 23:30 - the clk divider num of RTC_CLK"]
    #[inline(always)]
    pub fn ana_clk_div(&mut self) -> ANA_CLK_DIV_W<'_, SLOW_CLK_CONF_SPEC> {
        ANA_CLK_DIV_W::new(self, 23)
    }
    #[doc = "Bit 31 - flag rtc_slow_clk_next_edge"]
    #[inline(always)]
    pub fn slow_clk_next_edge(&mut self) -> SLOW_CLK_NEXT_EDGE_W<'_, SLOW_CLK_CONF_SPEC> {
        SLOW_CLK_NEXT_EDGE_W::new(self, 31)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`slow_clk_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slow_clk_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLOW_CLK_CONF_SPEC;
impl crate::RegisterSpec for SLOW_CLK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slow_clk_conf::R`](R) reader structure"]
impl crate::Readable for SLOW_CLK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slow_clk_conf::W`](W) writer structure"]
impl crate::Writable for SLOW_CLK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLOW_CLK_CONF to value 0x0040_0000"]
impl crate::Resettable for SLOW_CLK_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0040_0000;
}
