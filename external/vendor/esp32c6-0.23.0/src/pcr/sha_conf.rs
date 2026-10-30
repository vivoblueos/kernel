#[doc = "Register `SHA_CONF` reader"]
pub type R = crate::R<SHA_CONF_SPEC>;
#[doc = "Register `SHA_CONF` writer"]
pub type W = crate::W<SHA_CONF_SPEC>;
#[doc = "Field `SHA_CLK_EN` reader - Set 1 to enable sha clock"]
pub type SHA_CLK_EN_R = crate::BitReader;
#[doc = "Field `SHA_CLK_EN` writer - Set 1 to enable sha clock"]
pub type SHA_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SHA_RST_EN` reader - Set 0 to reset sha module"]
pub type SHA_RST_EN_R = crate::BitReader;
#[doc = "Field `SHA_RST_EN` writer - Set 0 to reset sha module"]
pub type SHA_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable sha clock"]
    #[inline(always)]
    pub fn sha_clk_en(&self) -> SHA_CLK_EN_R {
        SHA_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset sha module"]
    #[inline(always)]
    pub fn sha_rst_en(&self) -> SHA_RST_EN_R {
        SHA_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SHA_CONF")
            .field("sha_clk_en", &self.sha_clk_en())
            .field("sha_rst_en", &self.sha_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable sha clock"]
    #[inline(always)]
    pub fn sha_clk_en(&mut self) -> SHA_CLK_EN_W<'_, SHA_CONF_SPEC> {
        SHA_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset sha module"]
    #[inline(always)]
    pub fn sha_rst_en(&mut self) -> SHA_RST_EN_W<'_, SHA_CONF_SPEC> {
        SHA_RST_EN_W::new(self, 1)
    }
}
#[doc = "SHA configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sha_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sha_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SHA_CONF_SPEC;
impl crate::RegisterSpec for SHA_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sha_conf::R`](R) reader structure"]
impl crate::Readable for SHA_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sha_conf::W`](W) writer structure"]
impl crate::Writable for SHA_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SHA_CONF to value 0x01"]
impl crate::Resettable for SHA_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
