#[doc = "Register `TRACE_CONF` reader"]
pub type R = crate::R<TRACE_CONF_SPEC>;
#[doc = "Register `TRACE_CONF` writer"]
pub type W = crate::W<TRACE_CONF_SPEC>;
#[doc = "Field `TRACE_CLK_EN` reader - Set 1 to enable trace clock"]
pub type TRACE_CLK_EN_R = crate::BitReader;
#[doc = "Field `TRACE_CLK_EN` writer - Set 1 to enable trace clock"]
pub type TRACE_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TRACE_RST_EN` reader - Set 0 to reset trace module"]
pub type TRACE_RST_EN_R = crate::BitReader;
#[doc = "Field `TRACE_RST_EN` writer - Set 0 to reset trace module"]
pub type TRACE_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable trace clock"]
    #[inline(always)]
    pub fn trace_clk_en(&self) -> TRACE_CLK_EN_R {
        TRACE_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset trace module"]
    #[inline(always)]
    pub fn trace_rst_en(&self) -> TRACE_RST_EN_R {
        TRACE_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TRACE_CONF")
            .field("trace_clk_en", &self.trace_clk_en())
            .field("trace_rst_en", &self.trace_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable trace clock"]
    #[inline(always)]
    pub fn trace_clk_en(&mut self) -> TRACE_CLK_EN_W<'_, TRACE_CONF_SPEC> {
        TRACE_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset trace module"]
    #[inline(always)]
    pub fn trace_rst_en(&mut self) -> TRACE_RST_EN_W<'_, TRACE_CONF_SPEC> {
        TRACE_RST_EN_W::new(self, 1)
    }
}
#[doc = "TRACE configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`trace_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`trace_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TRACE_CONF_SPEC;
impl crate::RegisterSpec for TRACE_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`trace_conf::R`](R) reader structure"]
impl crate::Readable for TRACE_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`trace_conf::W`](W) writer structure"]
impl crate::Writable for TRACE_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TRACE_CONF to value 0x01"]
impl crate::Resettable for TRACE_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
