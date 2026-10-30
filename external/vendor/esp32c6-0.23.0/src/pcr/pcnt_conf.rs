#[doc = "Register `PCNT_CONF` reader"]
pub type R = crate::R<PCNT_CONF_SPEC>;
#[doc = "Register `PCNT_CONF` writer"]
pub type W = crate::W<PCNT_CONF_SPEC>;
#[doc = "Field `PCNT_CLK_EN` reader - Set 1 to enable pcnt clock"]
pub type PCNT_CLK_EN_R = crate::BitReader;
#[doc = "Field `PCNT_CLK_EN` writer - Set 1 to enable pcnt clock"]
pub type PCNT_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PCNT_RST_EN` reader - Set 0 to reset pcnt module"]
pub type PCNT_RST_EN_R = crate::BitReader;
#[doc = "Field `PCNT_RST_EN` writer - Set 0 to reset pcnt module"]
pub type PCNT_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable pcnt clock"]
    #[inline(always)]
    pub fn pcnt_clk_en(&self) -> PCNT_CLK_EN_R {
        PCNT_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset pcnt module"]
    #[inline(always)]
    pub fn pcnt_rst_en(&self) -> PCNT_RST_EN_R {
        PCNT_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PCNT_CONF")
            .field("pcnt_clk_en", &self.pcnt_clk_en())
            .field("pcnt_rst_en", &self.pcnt_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable pcnt clock"]
    #[inline(always)]
    pub fn pcnt_clk_en(&mut self) -> PCNT_CLK_EN_W<'_, PCNT_CONF_SPEC> {
        PCNT_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset pcnt module"]
    #[inline(always)]
    pub fn pcnt_rst_en(&mut self) -> PCNT_RST_EN_W<'_, PCNT_CONF_SPEC> {
        PCNT_RST_EN_W::new(self, 1)
    }
}
#[doc = "PCNT configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`pcnt_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pcnt_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PCNT_CONF_SPEC;
impl crate::RegisterSpec for PCNT_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pcnt_conf::R`](R) reader structure"]
impl crate::Readable for PCNT_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`pcnt_conf::W`](W) writer structure"]
impl crate::Writable for PCNT_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PCNT_CONF to value 0x01"]
impl crate::Resettable for PCNT_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
