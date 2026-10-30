#[doc = "Register `TWAI1_CONF` reader"]
pub type R = crate::R<TWAI1_CONF_SPEC>;
#[doc = "Register `TWAI1_CONF` writer"]
pub type W = crate::W<TWAI1_CONF_SPEC>;
#[doc = "Field `TWAI1_CLK_EN` reader - Set 1 to enable twai1 apb clock"]
pub type TWAI1_CLK_EN_R = crate::BitReader;
#[doc = "Field `TWAI1_CLK_EN` writer - Set 1 to enable twai1 apb clock"]
pub type TWAI1_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TWAI1_RST_EN` reader - Set 0 to reset twai1 module"]
pub type TWAI1_RST_EN_R = crate::BitReader;
#[doc = "Field `TWAI1_RST_EN` writer - Set 0 to reset twai1 module"]
pub type TWAI1_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable twai1 apb clock"]
    #[inline(always)]
    pub fn twai1_clk_en(&self) -> TWAI1_CLK_EN_R {
        TWAI1_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset twai1 module"]
    #[inline(always)]
    pub fn twai1_rst_en(&self) -> TWAI1_RST_EN_R {
        TWAI1_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TWAI1_CONF")
            .field("twai1_clk_en", &self.twai1_clk_en())
            .field("twai1_rst_en", &self.twai1_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable twai1 apb clock"]
    #[inline(always)]
    pub fn twai1_clk_en(&mut self) -> TWAI1_CLK_EN_W<'_, TWAI1_CONF_SPEC> {
        TWAI1_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset twai1 module"]
    #[inline(always)]
    pub fn twai1_rst_en(&mut self) -> TWAI1_RST_EN_W<'_, TWAI1_CONF_SPEC> {
        TWAI1_RST_EN_W::new(self, 1)
    }
}
#[doc = "TWAI1 configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`twai1_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`twai1_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TWAI1_CONF_SPEC;
impl crate::RegisterSpec for TWAI1_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`twai1_conf::R`](R) reader structure"]
impl crate::Readable for TWAI1_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`twai1_conf::W`](W) writer structure"]
impl crate::Writable for TWAI1_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TWAI1_CONF to value 0x01"]
impl crate::Resettable for TWAI1_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
