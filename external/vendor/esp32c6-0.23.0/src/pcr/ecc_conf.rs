#[doc = "Register `ECC_CONF` reader"]
pub type R = crate::R<ECC_CONF_SPEC>;
#[doc = "Register `ECC_CONF` writer"]
pub type W = crate::W<ECC_CONF_SPEC>;
#[doc = "Field `ECC_CLK_EN` reader - Set 1 to enable ecc clock"]
pub type ECC_CLK_EN_R = crate::BitReader;
#[doc = "Field `ECC_CLK_EN` writer - Set 1 to enable ecc clock"]
pub type ECC_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ECC_RST_EN` reader - Set 0 to reset ecc module"]
pub type ECC_RST_EN_R = crate::BitReader;
#[doc = "Field `ECC_RST_EN` writer - Set 0 to reset ecc module"]
pub type ECC_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable ecc clock"]
    #[inline(always)]
    pub fn ecc_clk_en(&self) -> ECC_CLK_EN_R {
        ECC_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset ecc module"]
    #[inline(always)]
    pub fn ecc_rst_en(&self) -> ECC_RST_EN_R {
        ECC_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ECC_CONF")
            .field("ecc_clk_en", &self.ecc_clk_en())
            .field("ecc_rst_en", &self.ecc_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable ecc clock"]
    #[inline(always)]
    pub fn ecc_clk_en(&mut self) -> ECC_CLK_EN_W<'_, ECC_CONF_SPEC> {
        ECC_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset ecc module"]
    #[inline(always)]
    pub fn ecc_rst_en(&mut self) -> ECC_RST_EN_W<'_, ECC_CONF_SPEC> {
        ECC_RST_EN_W::new(self, 1)
    }
}
#[doc = "ECC configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ecc_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ecc_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ECC_CONF_SPEC;
impl crate::RegisterSpec for ECC_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ecc_conf::R`](R) reader structure"]
impl crate::Readable for ECC_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ecc_conf::W`](W) writer structure"]
impl crate::Writable for ECC_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ECC_CONF to value 0x01"]
impl crate::Resettable for ECC_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
