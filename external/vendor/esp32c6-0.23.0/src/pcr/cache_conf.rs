#[doc = "Register `CACHE_CONF` reader"]
pub type R = crate::R<CACHE_CONF_SPEC>;
#[doc = "Register `CACHE_CONF` writer"]
pub type W = crate::W<CACHE_CONF_SPEC>;
#[doc = "Field `CACHE_CLK_EN` reader - Set 1 to enable cache clock"]
pub type CACHE_CLK_EN_R = crate::BitReader;
#[doc = "Field `CACHE_CLK_EN` writer - Set 1 to enable cache clock"]
pub type CACHE_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CACHE_RST_EN` reader - Set 0 to reset cache module"]
pub type CACHE_RST_EN_R = crate::BitReader;
#[doc = "Field `CACHE_RST_EN` writer - Set 0 to reset cache module"]
pub type CACHE_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable cache clock"]
    #[inline(always)]
    pub fn cache_clk_en(&self) -> CACHE_CLK_EN_R {
        CACHE_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset cache module"]
    #[inline(always)]
    pub fn cache_rst_en(&self) -> CACHE_RST_EN_R {
        CACHE_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_CONF")
            .field("cache_clk_en", &self.cache_clk_en())
            .field("cache_rst_en", &self.cache_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable cache clock"]
    #[inline(always)]
    pub fn cache_clk_en(&mut self) -> CACHE_CLK_EN_W<'_, CACHE_CONF_SPEC> {
        CACHE_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset cache module"]
    #[inline(always)]
    pub fn cache_rst_en(&mut self) -> CACHE_RST_EN_W<'_, CACHE_CONF_SPEC> {
        CACHE_RST_EN_W::new(self, 1)
    }
}
#[doc = "CACHE configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_CONF_SPEC;
impl crate::RegisterSpec for CACHE_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_conf::R`](R) reader structure"]
impl crate::Readable for CACHE_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cache_conf::W`](W) writer structure"]
impl crate::Writable for CACHE_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CACHE_CONF to value 0x01"]
impl crate::Resettable for CACHE_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
