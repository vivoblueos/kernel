#[doc = "Register `REGDMA_CONF` reader"]
pub type R = crate::R<REGDMA_CONF_SPEC>;
#[doc = "Register `REGDMA_CONF` writer"]
pub type W = crate::W<REGDMA_CONF_SPEC>;
#[doc = "Field `REGDMA_CLK_EN` reader - Set 1 to enable regdma clock"]
pub type REGDMA_CLK_EN_R = crate::BitReader;
#[doc = "Field `REGDMA_CLK_EN` writer - Set 1 to enable regdma clock"]
pub type REGDMA_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `REGDMA_RST_EN` reader - Set 0 to reset regdma module"]
pub type REGDMA_RST_EN_R = crate::BitReader;
#[doc = "Field `REGDMA_RST_EN` writer - Set 0 to reset regdma module"]
pub type REGDMA_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable regdma clock"]
    #[inline(always)]
    pub fn regdma_clk_en(&self) -> REGDMA_CLK_EN_R {
        REGDMA_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset regdma module"]
    #[inline(always)]
    pub fn regdma_rst_en(&self) -> REGDMA_RST_EN_R {
        REGDMA_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("REGDMA_CONF")
            .field("regdma_clk_en", &self.regdma_clk_en())
            .field("regdma_rst_en", &self.regdma_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable regdma clock"]
    #[inline(always)]
    pub fn regdma_clk_en(&mut self) -> REGDMA_CLK_EN_W<'_, REGDMA_CONF_SPEC> {
        REGDMA_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset regdma module"]
    #[inline(always)]
    pub fn regdma_rst_en(&mut self) -> REGDMA_RST_EN_W<'_, REGDMA_CONF_SPEC> {
        REGDMA_RST_EN_W::new(self, 1)
    }
}
#[doc = "REGDMA configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`regdma_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`regdma_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REGDMA_CONF_SPEC;
impl crate::RegisterSpec for REGDMA_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`regdma_conf::R`](R) reader structure"]
impl crate::Readable for REGDMA_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`regdma_conf::W`](W) writer structure"]
impl crate::Writable for REGDMA_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets REGDMA_CONF to value 0"]
impl crate::Resettable for REGDMA_CONF_SPEC {}
