#[doc = "Register `RSA_CONF` reader"]
pub type R = crate::R<RSA_CONF_SPEC>;
#[doc = "Register `RSA_CONF` writer"]
pub type W = crate::W<RSA_CONF_SPEC>;
#[doc = "Field `RSA_CLK_EN` reader - Set 1 to enable rsa clock"]
pub type RSA_CLK_EN_R = crate::BitReader;
#[doc = "Field `RSA_CLK_EN` writer - Set 1 to enable rsa clock"]
pub type RSA_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RSA_RST_EN` reader - Set 0 to reset rsa module"]
pub type RSA_RST_EN_R = crate::BitReader;
#[doc = "Field `RSA_RST_EN` writer - Set 0 to reset rsa module"]
pub type RSA_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable rsa clock"]
    #[inline(always)]
    pub fn rsa_clk_en(&self) -> RSA_CLK_EN_R {
        RSA_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset rsa module"]
    #[inline(always)]
    pub fn rsa_rst_en(&self) -> RSA_RST_EN_R {
        RSA_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RSA_CONF")
            .field("rsa_clk_en", &self.rsa_clk_en())
            .field("rsa_rst_en", &self.rsa_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable rsa clock"]
    #[inline(always)]
    pub fn rsa_clk_en(&mut self) -> RSA_CLK_EN_W<'_, RSA_CONF_SPEC> {
        RSA_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset rsa module"]
    #[inline(always)]
    pub fn rsa_rst_en(&mut self) -> RSA_RST_EN_W<'_, RSA_CONF_SPEC> {
        RSA_RST_EN_W::new(self, 1)
    }
}
#[doc = "RSA configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`rsa_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rsa_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RSA_CONF_SPEC;
impl crate::RegisterSpec for RSA_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rsa_conf::R`](R) reader structure"]
impl crate::Readable for RSA_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rsa_conf::W`](W) writer structure"]
impl crate::Writable for RSA_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RSA_CONF to value 0x01"]
impl crate::Resettable for RSA_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
