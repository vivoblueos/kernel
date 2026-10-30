#[doc = "Register `SLCCONF1` reader"]
pub type R = crate::R<SLCCONF1_SPEC>;
#[doc = "Register `SLCCONF1` writer"]
pub type W = crate::W<SLCCONF1_SPEC>;
#[doc = "Field `SDIO_SDIO_CMD_HOLD_EN` reader - Please initialize to 0, and do not modify it."]
pub type SDIO_SDIO_CMD_HOLD_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SDIO_CMD_HOLD_EN` writer - Please initialize to 0, and do not modify it."]
pub type SDIO_SDIO_CMD_HOLD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_LEN_AUTO_CLR` reader - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC0_LEN_AUTO_CLR_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_LEN_AUTO_CLR` writer - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC0_LEN_AUTO_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TX_STITCH_EN` reader - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC0_TX_STITCH_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_STITCH_EN` writer - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC0_TX_STITCH_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_STITCH_EN` reader - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC0_RX_STITCH_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_STITCH_EN` writer - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC0_RX_STITCH_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_HOST_INT_LEVEL_SEL` reader - Configures the polarity of interrupt to host."]
pub type SDIO_HOST_INT_LEVEL_SEL_R = crate::BitReader;
#[doc = "Field `SDIO_HOST_INT_LEVEL_SEL` writer - Configures the polarity of interrupt to host."]
pub type SDIO_HOST_INT_LEVEL_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_TX_STITCH_EN` reader - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC1_TX_STITCH_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_TX_STITCH_EN` writer - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC1_TX_STITCH_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RX_STITCH_EN` reader - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC1_RX_STITCH_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RX_STITCH_EN` writer - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC1_RX_STITCH_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 3 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_sdio_cmd_hold_en(&self) -> SDIO_SDIO_CMD_HOLD_EN_R {
        SDIO_SDIO_CMD_HOLD_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc0_len_auto_clr(&self) -> SDIO_SLC0_LEN_AUTO_CLR_R {
        SDIO_SLC0_LEN_AUTO_CLR_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc0_tx_stitch_en(&self) -> SDIO_SLC0_TX_STITCH_EN_R {
        SDIO_SLC0_TX_STITCH_EN_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc0_rx_stitch_en(&self) -> SDIO_SLC0_RX_STITCH_EN_R {
        SDIO_SLC0_RX_STITCH_EN_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 19 - Configures the polarity of interrupt to host."]
    #[inline(always)]
    pub fn sdio_host_int_level_sel(&self) -> SDIO_HOST_INT_LEVEL_SEL_R {
        SDIO_HOST_INT_LEVEL_SEL_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc1_tx_stitch_en(&self) -> SDIO_SLC1_TX_STITCH_EN_R {
        SDIO_SLC1_TX_STITCH_EN_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc1_rx_stitch_en(&self) -> SDIO_SLC1_RX_STITCH_EN_R {
        SDIO_SLC1_RX_STITCH_EN_R::new(((self.bits >> 21) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLCCONF1")
            .field("sdio_sdio_cmd_hold_en", &self.sdio_sdio_cmd_hold_en())
            .field("sdio_slc0_len_auto_clr", &self.sdio_slc0_len_auto_clr())
            .field("sdio_slc0_tx_stitch_en", &self.sdio_slc0_tx_stitch_en())
            .field("sdio_slc0_rx_stitch_en", &self.sdio_slc0_rx_stitch_en())
            .field("sdio_host_int_level_sel", &self.sdio_host_int_level_sel())
            .field("sdio_slc1_tx_stitch_en", &self.sdio_slc1_tx_stitch_en())
            .field("sdio_slc1_rx_stitch_en", &self.sdio_slc1_rx_stitch_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 3 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_sdio_cmd_hold_en(&mut self) -> SDIO_SDIO_CMD_HOLD_EN_W<'_, SLCCONF1_SPEC> {
        SDIO_SDIO_CMD_HOLD_EN_W::new(self, 3)
    }
    #[doc = "Bit 4 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc0_len_auto_clr(&mut self) -> SDIO_SLC0_LEN_AUTO_CLR_W<'_, SLCCONF1_SPEC> {
        SDIO_SLC0_LEN_AUTO_CLR_W::new(self, 4)
    }
    #[doc = "Bit 5 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc0_tx_stitch_en(&mut self) -> SDIO_SLC0_TX_STITCH_EN_W<'_, SLCCONF1_SPEC> {
        SDIO_SLC0_TX_STITCH_EN_W::new(self, 5)
    }
    #[doc = "Bit 6 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc0_rx_stitch_en(&mut self) -> SDIO_SLC0_RX_STITCH_EN_W<'_, SLCCONF1_SPEC> {
        SDIO_SLC0_RX_STITCH_EN_W::new(self, 6)
    }
    #[doc = "Bit 19 - Configures the polarity of interrupt to host."]
    #[inline(always)]
    pub fn sdio_host_int_level_sel(&mut self) -> SDIO_HOST_INT_LEVEL_SEL_W<'_, SLCCONF1_SPEC> {
        SDIO_HOST_INT_LEVEL_SEL_W::new(self, 19)
    }
    #[doc = "Bit 20 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc1_tx_stitch_en(&mut self) -> SDIO_SLC1_TX_STITCH_EN_W<'_, SLCCONF1_SPEC> {
        SDIO_SLC1_TX_STITCH_EN_W::new(self, 20)
    }
    #[doc = "Bit 21 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc1_rx_stitch_en(&mut self) -> SDIO_SLC1_RX_STITCH_EN_W<'_, SLCCONF1_SPEC> {
        SDIO_SLC1_RX_STITCH_EN_W::new(self, 21)
    }
}
#[doc = "DMA configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slcconf1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slcconf1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLCCONF1_SPEC;
impl crate::RegisterSpec for SLCCONF1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slcconf1::R`](R) reader structure"]
impl crate::Readable for SLCCONF1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slcconf1::W`](W) writer structure"]
impl crate::Writable for SLCCONF1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLCCONF1 to value 0x0030_0078"]
impl crate::Resettable for SLCCONF1_SPEC {
    const RESET_VALUE: u32 = 0x0030_0078;
}
