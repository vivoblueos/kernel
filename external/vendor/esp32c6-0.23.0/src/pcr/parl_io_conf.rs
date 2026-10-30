#[doc = "Register `PARL_IO_CONF` reader"]
pub type R = crate::R<PARL_IO_CONF_SPEC>;
#[doc = "Register `PARL_IO_CONF` writer"]
pub type W = crate::W<PARL_IO_CONF_SPEC>;
#[doc = "Field `PARL_CLK_EN` reader - Set 1 to enable parl apb clock"]
pub type PARL_CLK_EN_R = crate::BitReader;
#[doc = "Field `PARL_CLK_EN` writer - Set 1 to enable parl apb clock"]
pub type PARL_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PARL_RST_EN` reader - Set 0 to reset parl apb reg"]
pub type PARL_RST_EN_R = crate::BitReader;
#[doc = "Field `PARL_RST_EN` writer - Set 0 to reset parl apb reg"]
pub type PARL_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable parl apb clock"]
    #[inline(always)]
    pub fn parl_clk_en(&self) -> PARL_CLK_EN_R {
        PARL_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset parl apb reg"]
    #[inline(always)]
    pub fn parl_rst_en(&self) -> PARL_RST_EN_R {
        PARL_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PARL_IO_CONF")
            .field("parl_clk_en", &self.parl_clk_en())
            .field("parl_rst_en", &self.parl_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable parl apb clock"]
    #[inline(always)]
    pub fn parl_clk_en(&mut self) -> PARL_CLK_EN_W<'_, PARL_IO_CONF_SPEC> {
        PARL_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset parl apb reg"]
    #[inline(always)]
    pub fn parl_rst_en(&mut self) -> PARL_RST_EN_W<'_, PARL_IO_CONF_SPEC> {
        PARL_RST_EN_W::new(self, 1)
    }
}
#[doc = "PARL_IO configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`parl_io_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`parl_io_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PARL_IO_CONF_SPEC;
impl crate::RegisterSpec for PARL_IO_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`parl_io_conf::R`](R) reader structure"]
impl crate::Readable for PARL_IO_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`parl_io_conf::W`](W) writer structure"]
impl crate::Writable for PARL_IO_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PARL_IO_CONF to value 0x01"]
impl crate::Resettable for PARL_IO_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
