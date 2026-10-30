#[doc = "Register `RETENTION_CONF` reader"]
pub type R = crate::R<RETENTION_CONF_SPEC>;
#[doc = "Register `RETENTION_CONF` writer"]
pub type W = crate::W<RETENTION_CONF_SPEC>;
#[doc = "Field `RETENTION_CLK_EN` reader - Set 1 to enable retention clock"]
pub type RETENTION_CLK_EN_R = crate::BitReader;
#[doc = "Field `RETENTION_CLK_EN` writer - Set 1 to enable retention clock"]
pub type RETENTION_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RETENTION_RST_EN` reader - Set 0 to reset retention module"]
pub type RETENTION_RST_EN_R = crate::BitReader;
#[doc = "Field `RETENTION_RST_EN` writer - Set 0 to reset retention module"]
pub type RETENTION_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable retention clock"]
    #[inline(always)]
    pub fn retention_clk_en(&self) -> RETENTION_CLK_EN_R {
        RETENTION_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset retention module"]
    #[inline(always)]
    pub fn retention_rst_en(&self) -> RETENTION_RST_EN_R {
        RETENTION_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RETENTION_CONF")
            .field("retention_clk_en", &self.retention_clk_en())
            .field("retention_rst_en", &self.retention_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable retention clock"]
    #[inline(always)]
    pub fn retention_clk_en(&mut self) -> RETENTION_CLK_EN_W<'_, RETENTION_CONF_SPEC> {
        RETENTION_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset retention module"]
    #[inline(always)]
    pub fn retention_rst_en(&mut self) -> RETENTION_RST_EN_W<'_, RETENTION_CONF_SPEC> {
        RETENTION_RST_EN_W::new(self, 1)
    }
}
#[doc = "retention configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`retention_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`retention_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RETENTION_CONF_SPEC;
impl crate::RegisterSpec for RETENTION_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`retention_conf::R`](R) reader structure"]
impl crate::Readable for RETENTION_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`retention_conf::W`](W) writer structure"]
impl crate::Writable for RETENTION_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RETENTION_CONF to value 0"]
impl crate::Resettable for RETENTION_CONF_SPEC {}
