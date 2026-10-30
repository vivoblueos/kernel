#[doc = "Register `ASSIST_CONF` reader"]
pub type R = crate::R<ASSIST_CONF_SPEC>;
#[doc = "Register `ASSIST_CONF` writer"]
pub type W = crate::W<ASSIST_CONF_SPEC>;
#[doc = "Field `ASSIST_CLK_EN` reader - Set 1 to enable assist clock"]
pub type ASSIST_CLK_EN_R = crate::BitReader;
#[doc = "Field `ASSIST_CLK_EN` writer - Set 1 to enable assist clock"]
pub type ASSIST_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ASSIST_RST_EN` reader - Set 0 to reset assist module"]
pub type ASSIST_RST_EN_R = crate::BitReader;
#[doc = "Field `ASSIST_RST_EN` writer - Set 0 to reset assist module"]
pub type ASSIST_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable assist clock"]
    #[inline(always)]
    pub fn assist_clk_en(&self) -> ASSIST_CLK_EN_R {
        ASSIST_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset assist module"]
    #[inline(always)]
    pub fn assist_rst_en(&self) -> ASSIST_RST_EN_R {
        ASSIST_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ASSIST_CONF")
            .field("assist_clk_en", &self.assist_clk_en())
            .field("assist_rst_en", &self.assist_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable assist clock"]
    #[inline(always)]
    pub fn assist_clk_en(&mut self) -> ASSIST_CLK_EN_W<'_, ASSIST_CONF_SPEC> {
        ASSIST_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset assist module"]
    #[inline(always)]
    pub fn assist_rst_en(&mut self) -> ASSIST_RST_EN_W<'_, ASSIST_CONF_SPEC> {
        ASSIST_RST_EN_W::new(self, 1)
    }
}
#[doc = "ASSIST configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`assist_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`assist_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ASSIST_CONF_SPEC;
impl crate::RegisterSpec for ASSIST_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`assist_conf::R`](R) reader structure"]
impl crate::Readable for ASSIST_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`assist_conf::W`](W) writer structure"]
impl crate::Writable for ASSIST_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ASSIST_CONF to value 0x01"]
impl crate::Resettable for ASSIST_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
