#[doc = "Register `PVT_MONITOR_CONF` reader"]
pub type R = crate::R<PVT_MONITOR_CONF_SPEC>;
#[doc = "Register `PVT_MONITOR_CONF` writer"]
pub type W = crate::W<PVT_MONITOR_CONF_SPEC>;
#[doc = "Field `PVT_MONITOR_CLK_EN` reader - Set 1 to enable apb clock of pvt module"]
pub type PVT_MONITOR_CLK_EN_R = crate::BitReader;
#[doc = "Field `PVT_MONITOR_CLK_EN` writer - Set 1 to enable apb clock of pvt module"]
pub type PVT_MONITOR_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PVT_MONITOR_RST_EN` reader - Set 0 to reset all pvt monitor module"]
pub type PVT_MONITOR_RST_EN_R = crate::BitReader;
#[doc = "Field `PVT_MONITOR_RST_EN` writer - Set 0 to reset all pvt monitor module"]
pub type PVT_MONITOR_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PVT_MONITOR_SITE1_CLK_EN` reader - Set 1 to enable function clock of modem pvt module"]
pub type PVT_MONITOR_SITE1_CLK_EN_R = crate::BitReader;
#[doc = "Field `PVT_MONITOR_SITE1_CLK_EN` writer - Set 1 to enable function clock of modem pvt module"]
pub type PVT_MONITOR_SITE1_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PVT_MONITOR_SITE2_CLK_EN` reader - Set 1 to enable function clock of cpu pvt module"]
pub type PVT_MONITOR_SITE2_CLK_EN_R = crate::BitReader;
#[doc = "Field `PVT_MONITOR_SITE2_CLK_EN` writer - Set 1 to enable function clock of cpu pvt module"]
pub type PVT_MONITOR_SITE2_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PVT_MONITOR_SITE3_CLK_EN` reader - Set 1 to enable function clock of hp_peri pvt module"]
pub type PVT_MONITOR_SITE3_CLK_EN_R = crate::BitReader;
#[doc = "Field `PVT_MONITOR_SITE3_CLK_EN` writer - Set 1 to enable function clock of hp_peri pvt module"]
pub type PVT_MONITOR_SITE3_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable apb clock of pvt module"]
    #[inline(always)]
    pub fn pvt_monitor_clk_en(&self) -> PVT_MONITOR_CLK_EN_R {
        PVT_MONITOR_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset all pvt monitor module"]
    #[inline(always)]
    pub fn pvt_monitor_rst_en(&self) -> PVT_MONITOR_RST_EN_R {
        PVT_MONITOR_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set 1 to enable function clock of modem pvt module"]
    #[inline(always)]
    pub fn pvt_monitor_site1_clk_en(&self) -> PVT_MONITOR_SITE1_CLK_EN_R {
        PVT_MONITOR_SITE1_CLK_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Set 1 to enable function clock of cpu pvt module"]
    #[inline(always)]
    pub fn pvt_monitor_site2_clk_en(&self) -> PVT_MONITOR_SITE2_CLK_EN_R {
        PVT_MONITOR_SITE2_CLK_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Set 1 to enable function clock of hp_peri pvt module"]
    #[inline(always)]
    pub fn pvt_monitor_site3_clk_en(&self) -> PVT_MONITOR_SITE3_CLK_EN_R {
        PVT_MONITOR_SITE3_CLK_EN_R::new(((self.bits >> 4) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PVT_MONITOR_CONF")
            .field("pvt_monitor_clk_en", &self.pvt_monitor_clk_en())
            .field("pvt_monitor_rst_en", &self.pvt_monitor_rst_en())
            .field("pvt_monitor_site1_clk_en", &self.pvt_monitor_site1_clk_en())
            .field("pvt_monitor_site2_clk_en", &self.pvt_monitor_site2_clk_en())
            .field("pvt_monitor_site3_clk_en", &self.pvt_monitor_site3_clk_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable apb clock of pvt module"]
    #[inline(always)]
    pub fn pvt_monitor_clk_en(&mut self) -> PVT_MONITOR_CLK_EN_W<'_, PVT_MONITOR_CONF_SPEC> {
        PVT_MONITOR_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset all pvt monitor module"]
    #[inline(always)]
    pub fn pvt_monitor_rst_en(&mut self) -> PVT_MONITOR_RST_EN_W<'_, PVT_MONITOR_CONF_SPEC> {
        PVT_MONITOR_RST_EN_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set 1 to enable function clock of modem pvt module"]
    #[inline(always)]
    pub fn pvt_monitor_site1_clk_en(
        &mut self,
    ) -> PVT_MONITOR_SITE1_CLK_EN_W<'_, PVT_MONITOR_CONF_SPEC> {
        PVT_MONITOR_SITE1_CLK_EN_W::new(self, 2)
    }
    #[doc = "Bit 3 - Set 1 to enable function clock of cpu pvt module"]
    #[inline(always)]
    pub fn pvt_monitor_site2_clk_en(
        &mut self,
    ) -> PVT_MONITOR_SITE2_CLK_EN_W<'_, PVT_MONITOR_CONF_SPEC> {
        PVT_MONITOR_SITE2_CLK_EN_W::new(self, 3)
    }
    #[doc = "Bit 4 - Set 1 to enable function clock of hp_peri pvt module"]
    #[inline(always)]
    pub fn pvt_monitor_site3_clk_en(
        &mut self,
    ) -> PVT_MONITOR_SITE3_CLK_EN_W<'_, PVT_MONITOR_CONF_SPEC> {
        PVT_MONITOR_SITE3_CLK_EN_W::new(self, 4)
    }
}
#[doc = "PVT_MONITOR configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`pvt_monitor_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pvt_monitor_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PVT_MONITOR_CONF_SPEC;
impl crate::RegisterSpec for PVT_MONITOR_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pvt_monitor_conf::R`](R) reader structure"]
impl crate::Readable for PVT_MONITOR_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`pvt_monitor_conf::W`](W) writer structure"]
impl crate::Writable for PVT_MONITOR_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PVT_MONITOR_CONF to value 0x1d"]
impl crate::Resettable for PVT_MONITOR_CONF_SPEC {
    const RESET_VALUE: u32 = 0x1d;
}
