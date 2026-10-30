#[doc = "Register `REGDMA_CLK_CONF` reader"]
pub type R = crate::R<REGDMA_CLK_CONF_SPEC>;
#[doc = "Register `REGDMA_CLK_CONF` writer"]
pub type W = crate::W<REGDMA_CLK_CONF_SPEC>;
#[doc = "Field `CLK_EN` reader - clock enable"]
pub type CLK_EN_R = crate::BitReader;
#[doc = "Field `CLK_EN` writer - clock enable"]
pub type CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - clock enable"]
    #[inline(always)]
    pub fn clk_en(&self) -> CLK_EN_R {
        CLK_EN_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("REGDMA_CLK_CONF")
            .field("clk_en", &self.clk_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - clock enable"]
    #[inline(always)]
    pub fn clk_en(&mut self) -> CLK_EN_W<'_, REGDMA_CLK_CONF_SPEC> {
        CLK_EN_W::new(self, 0)
    }
}
#[doc = "Clock control register\n\nYou can [`read`](crate::Reg::read) this register and get [`regdma_clk_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`regdma_clk_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REGDMA_CLK_CONF_SPEC;
impl crate::RegisterSpec for REGDMA_CLK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`regdma_clk_conf::R`](R) reader structure"]
impl crate::Readable for REGDMA_CLK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`regdma_clk_conf::W`](W) writer structure"]
impl crate::Writable for REGDMA_CLK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets REGDMA_CLK_CONF to value 0"]
impl crate::Resettable for REGDMA_CLK_CONF_SPEC {}
