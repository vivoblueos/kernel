#[doc = "Register `INTMTX_CONF` reader"]
pub type R = crate::R<INTMTX_CONF_SPEC>;
#[doc = "Register `INTMTX_CONF` writer"]
pub type W = crate::W<INTMTX_CONF_SPEC>;
#[doc = "Field `INTMTX_CLK_EN` reader - Set 1 to enable intmtx clock"]
pub type INTMTX_CLK_EN_R = crate::BitReader;
#[doc = "Field `INTMTX_CLK_EN` writer - Set 1 to enable intmtx clock"]
pub type INTMTX_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `INTMTX_RST_EN` reader - Set 0 to reset intmtx module"]
pub type INTMTX_RST_EN_R = crate::BitReader;
#[doc = "Field `INTMTX_RST_EN` writer - Set 0 to reset intmtx module"]
pub type INTMTX_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable intmtx clock"]
    #[inline(always)]
    pub fn intmtx_clk_en(&self) -> INTMTX_CLK_EN_R {
        INTMTX_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset intmtx module"]
    #[inline(always)]
    pub fn intmtx_rst_en(&self) -> INTMTX_RST_EN_R {
        INTMTX_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INTMTX_CONF")
            .field("intmtx_clk_en", &self.intmtx_clk_en())
            .field("intmtx_rst_en", &self.intmtx_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable intmtx clock"]
    #[inline(always)]
    pub fn intmtx_clk_en(&mut self) -> INTMTX_CLK_EN_W<'_, INTMTX_CONF_SPEC> {
        INTMTX_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset intmtx module"]
    #[inline(always)]
    pub fn intmtx_rst_en(&mut self) -> INTMTX_RST_EN_W<'_, INTMTX_CONF_SPEC> {
        INTMTX_RST_EN_W::new(self, 1)
    }
}
#[doc = "INTMTX configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`intmtx_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`intmtx_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INTMTX_CONF_SPEC;
impl crate::RegisterSpec for INTMTX_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`intmtx_conf::R`](R) reader structure"]
impl crate::Readable for INTMTX_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`intmtx_conf::W`](W) writer structure"]
impl crate::Writable for INTMTX_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INTMTX_CONF to value 0x01"]
impl crate::Resettable for INTMTX_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
