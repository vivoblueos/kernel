#[doc = "Register `SDIO_SLAVE_ECO_CONF` reader"]
pub type R = crate::R<SDIO_SLAVE_ECO_CONF_SPEC>;
#[doc = "Register `SDIO_SLAVE_ECO_CONF` writer"]
pub type W = crate::W<SDIO_SLAVE_ECO_CONF_SPEC>;
#[doc = "Field `SDIO_SLAVE_RDN_RESULT` reader - redundant registers for sdio_slave"]
pub type SDIO_SLAVE_RDN_RESULT_R = crate::BitReader;
#[doc = "Field `SDIO_SLAVE_RDN_ENA` reader - redundant registers for sdio_slave"]
pub type SDIO_SLAVE_RDN_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLAVE_RDN_ENA` writer - redundant registers for sdio_slave"]
pub type SDIO_SLAVE_RDN_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLAVE_SDIO_CLK_RDN_RESULT` reader - redundant registers for sdio_slave"]
pub type SDIO_SLAVE_SDIO_CLK_RDN_RESULT_R = crate::BitReader;
#[doc = "Field `SDIO_SLAVE_SDIO_CLK_RDN_ENA` reader - redundant registers for sdio_slave"]
pub type SDIO_SLAVE_SDIO_CLK_RDN_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLAVE_SDIO_CLK_RDN_ENA` writer - redundant registers for sdio_slave"]
pub type SDIO_SLAVE_SDIO_CLK_RDN_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLAVE_SDCLK_PAD_RDN_RESULT` reader - redundant registers for sdio_slave"]
pub type SDIO_SLAVE_SDCLK_PAD_RDN_RESULT_R = crate::BitReader;
#[doc = "Field `SDIO_SLAVE_SDCLK_PAD_RDN_ENA` reader - redundant registers for sdio_slave"]
pub type SDIO_SLAVE_SDCLK_PAD_RDN_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLAVE_SDCLK_PAD_RDN_ENA` writer - redundant registers for sdio_slave"]
pub type SDIO_SLAVE_SDCLK_PAD_RDN_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - redundant registers for sdio_slave"]
    #[inline(always)]
    pub fn sdio_slave_rdn_result(&self) -> SDIO_SLAVE_RDN_RESULT_R {
        SDIO_SLAVE_RDN_RESULT_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - redundant registers for sdio_slave"]
    #[inline(always)]
    pub fn sdio_slave_rdn_ena(&self) -> SDIO_SLAVE_RDN_ENA_R {
        SDIO_SLAVE_RDN_ENA_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - redundant registers for sdio_slave"]
    #[inline(always)]
    pub fn sdio_slave_sdio_clk_rdn_result(&self) -> SDIO_SLAVE_SDIO_CLK_RDN_RESULT_R {
        SDIO_SLAVE_SDIO_CLK_RDN_RESULT_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - redundant registers for sdio_slave"]
    #[inline(always)]
    pub fn sdio_slave_sdio_clk_rdn_ena(&self) -> SDIO_SLAVE_SDIO_CLK_RDN_ENA_R {
        SDIO_SLAVE_SDIO_CLK_RDN_ENA_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - redundant registers for sdio_slave"]
    #[inline(always)]
    pub fn sdio_slave_sdclk_pad_rdn_result(&self) -> SDIO_SLAVE_SDCLK_PAD_RDN_RESULT_R {
        SDIO_SLAVE_SDCLK_PAD_RDN_RESULT_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - redundant registers for sdio_slave"]
    #[inline(always)]
    pub fn sdio_slave_sdclk_pad_rdn_ena(&self) -> SDIO_SLAVE_SDCLK_PAD_RDN_ENA_R {
        SDIO_SLAVE_SDCLK_PAD_RDN_ENA_R::new(((self.bits >> 5) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SDIO_SLAVE_ECO_CONF")
            .field("sdio_slave_rdn_result", &self.sdio_slave_rdn_result())
            .field("sdio_slave_rdn_ena", &self.sdio_slave_rdn_ena())
            .field(
                "sdio_slave_sdio_clk_rdn_result",
                &self.sdio_slave_sdio_clk_rdn_result(),
            )
            .field(
                "sdio_slave_sdio_clk_rdn_ena",
                &self.sdio_slave_sdio_clk_rdn_ena(),
            )
            .field(
                "sdio_slave_sdclk_pad_rdn_result",
                &self.sdio_slave_sdclk_pad_rdn_result(),
            )
            .field(
                "sdio_slave_sdclk_pad_rdn_ena",
                &self.sdio_slave_sdclk_pad_rdn_ena(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 1 - redundant registers for sdio_slave"]
    #[inline(always)]
    pub fn sdio_slave_rdn_ena(&mut self) -> SDIO_SLAVE_RDN_ENA_W<'_, SDIO_SLAVE_ECO_CONF_SPEC> {
        SDIO_SLAVE_RDN_ENA_W::new(self, 1)
    }
    #[doc = "Bit 3 - redundant registers for sdio_slave"]
    #[inline(always)]
    pub fn sdio_slave_sdio_clk_rdn_ena(
        &mut self,
    ) -> SDIO_SLAVE_SDIO_CLK_RDN_ENA_W<'_, SDIO_SLAVE_ECO_CONF_SPEC> {
        SDIO_SLAVE_SDIO_CLK_RDN_ENA_W::new(self, 3)
    }
    #[doc = "Bit 5 - redundant registers for sdio_slave"]
    #[inline(always)]
    pub fn sdio_slave_sdclk_pad_rdn_ena(
        &mut self,
    ) -> SDIO_SLAVE_SDCLK_PAD_RDN_ENA_W<'_, SDIO_SLAVE_ECO_CONF_SPEC> {
        SDIO_SLAVE_SDCLK_PAD_RDN_ENA_W::new(self, 5)
    }
}
#[doc = "sdio_slave redundant control registers\n\nYou can [`read`](crate::Reg::read) this register and get [`sdio_slave_eco_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sdio_slave_eco_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SDIO_SLAVE_ECO_CONF_SPEC;
impl crate::RegisterSpec for SDIO_SLAVE_ECO_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sdio_slave_eco_conf::R`](R) reader structure"]
impl crate::Readable for SDIO_SLAVE_ECO_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sdio_slave_eco_conf::W`](W) writer structure"]
impl crate::Writable for SDIO_SLAVE_ECO_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SDIO_SLAVE_ECO_CONF to value 0"]
impl crate::Resettable for SDIO_SLAVE_ECO_CONF_SPEC {}
