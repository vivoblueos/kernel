#[doc = "Register `AES_CONF` reader"]
pub type R = crate::R<AES_CONF_SPEC>;
#[doc = "Register `AES_CONF` writer"]
pub type W = crate::W<AES_CONF_SPEC>;
#[doc = "Field `AES_CLK_EN` reader - Set 1 to enable aes clock"]
pub type AES_CLK_EN_R = crate::BitReader;
#[doc = "Field `AES_CLK_EN` writer - Set 1 to enable aes clock"]
pub type AES_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AES_RST_EN` reader - Set 0 to reset aes module"]
pub type AES_RST_EN_R = crate::BitReader;
#[doc = "Field `AES_RST_EN` writer - Set 0 to reset aes module"]
pub type AES_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable aes clock"]
    #[inline(always)]
    pub fn aes_clk_en(&self) -> AES_CLK_EN_R {
        AES_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset aes module"]
    #[inline(always)]
    pub fn aes_rst_en(&self) -> AES_RST_EN_R {
        AES_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("AES_CONF")
            .field("aes_clk_en", &self.aes_clk_en())
            .field("aes_rst_en", &self.aes_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable aes clock"]
    #[inline(always)]
    pub fn aes_clk_en(&mut self) -> AES_CLK_EN_W<'_, AES_CONF_SPEC> {
        AES_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset aes module"]
    #[inline(always)]
    pub fn aes_rst_en(&mut self) -> AES_RST_EN_W<'_, AES_CONF_SPEC> {
        AES_RST_EN_W::new(self, 1)
    }
}
#[doc = "AES configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`aes_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`aes_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AES_CONF_SPEC;
impl crate::RegisterSpec for AES_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`aes_conf::R`](R) reader structure"]
impl crate::Readable for AES_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`aes_conf::W`](W) writer structure"]
impl crate::Writable for AES_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets AES_CONF to value 0x01"]
impl crate::Resettable for AES_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
