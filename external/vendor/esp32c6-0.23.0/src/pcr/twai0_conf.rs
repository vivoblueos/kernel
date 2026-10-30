#[doc = "Register `TWAI0_CONF` reader"]
pub type R = crate::R<TWAI0_CONF_SPEC>;
#[doc = "Register `TWAI0_CONF` writer"]
pub type W = crate::W<TWAI0_CONF_SPEC>;
#[doc = "Field `TWAI0_CLK_EN` reader - Set 1 to enable twai0 apb clock"]
pub type TWAI0_CLK_EN_R = crate::BitReader;
#[doc = "Field `TWAI0_CLK_EN` writer - Set 1 to enable twai0 apb clock"]
pub type TWAI0_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TWAI0_RST_EN` reader - Set 0 to reset twai0 module"]
pub type TWAI0_RST_EN_R = crate::BitReader;
#[doc = "Field `TWAI0_RST_EN` writer - Set 0 to reset twai0 module"]
pub type TWAI0_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable twai0 apb clock"]
    #[inline(always)]
    pub fn twai0_clk_en(&self) -> TWAI0_CLK_EN_R {
        TWAI0_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset twai0 module"]
    #[inline(always)]
    pub fn twai0_rst_en(&self) -> TWAI0_RST_EN_R {
        TWAI0_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TWAI0_CONF")
            .field("twai0_clk_en", &self.twai0_clk_en())
            .field("twai0_rst_en", &self.twai0_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable twai0 apb clock"]
    #[inline(always)]
    pub fn twai0_clk_en(&mut self) -> TWAI0_CLK_EN_W<'_, TWAI0_CONF_SPEC> {
        TWAI0_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset twai0 module"]
    #[inline(always)]
    pub fn twai0_rst_en(&mut self) -> TWAI0_RST_EN_W<'_, TWAI0_CONF_SPEC> {
        TWAI0_RST_EN_W::new(self, 1)
    }
}
#[doc = "TWAI0 configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`twai0_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`twai0_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TWAI0_CONF_SPEC;
impl crate::RegisterSpec for TWAI0_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`twai0_conf::R`](R) reader structure"]
impl crate::Readable for TWAI0_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`twai0_conf::W`](W) writer structure"]
impl crate::Writable for TWAI0_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TWAI0_CONF to value 0x01"]
impl crate::Resettable for TWAI0_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
