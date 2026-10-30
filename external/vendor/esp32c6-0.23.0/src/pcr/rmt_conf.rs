#[doc = "Register `RMT_CONF` reader"]
pub type R = crate::R<RMT_CONF_SPEC>;
#[doc = "Register `RMT_CONF` writer"]
pub type W = crate::W<RMT_CONF_SPEC>;
#[doc = "Field `RMT_CLK_EN` reader - Set 1 to enable rmt apb clock"]
pub type RMT_CLK_EN_R = crate::BitReader;
#[doc = "Field `RMT_CLK_EN` writer - Set 1 to enable rmt apb clock"]
pub type RMT_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RMT_RST_EN` reader - Set 0 to reset rmt module"]
pub type RMT_RST_EN_R = crate::BitReader;
#[doc = "Field `RMT_RST_EN` writer - Set 0 to reset rmt module"]
pub type RMT_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable rmt apb clock"]
    #[inline(always)]
    pub fn rmt_clk_en(&self) -> RMT_CLK_EN_R {
        RMT_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset rmt module"]
    #[inline(always)]
    pub fn rmt_rst_en(&self) -> RMT_RST_EN_R {
        RMT_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RMT_CONF")
            .field("rmt_clk_en", &self.rmt_clk_en())
            .field("rmt_rst_en", &self.rmt_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable rmt apb clock"]
    #[inline(always)]
    pub fn rmt_clk_en(&mut self) -> RMT_CLK_EN_W<'_, RMT_CONF_SPEC> {
        RMT_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset rmt module"]
    #[inline(always)]
    pub fn rmt_rst_en(&mut self) -> RMT_RST_EN_W<'_, RMT_CONF_SPEC> {
        RMT_RST_EN_W::new(self, 1)
    }
}
#[doc = "RMT configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`rmt_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rmt_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RMT_CONF_SPEC;
impl crate::RegisterSpec for RMT_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rmt_conf::R`](R) reader structure"]
impl crate::Readable for RMT_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rmt_conf::W`](W) writer structure"]
impl crate::Writable for RMT_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RMT_CONF to value 0x01"]
impl crate::Resettable for RMT_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
