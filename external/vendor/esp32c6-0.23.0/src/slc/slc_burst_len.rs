#[doc = "Register `SLC_BURST_LEN` reader"]
pub type R = crate::R<SLC_BURST_LEN_SPEC>;
#[doc = "Register `SLC_BURST_LEN` writer"]
pub type W = crate::W<SLC_BURST_LEN_SPEC>;
#[doc = "Field `SDIO_SLC0_TXDATA_BURST_LEN` reader - Configures SLC0 host to slave channel AHB burst type."]
pub type SDIO_SLC0_TXDATA_BURST_LEN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TXDATA_BURST_LEN` writer - Configures SLC0 host to slave channel AHB burst type."]
pub type SDIO_SLC0_TXDATA_BURST_LEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RXDATA_BURST_LEN` reader - Configures SLC0 slave to host channel AHB burst type."]
pub type SDIO_SLC0_RXDATA_BURST_LEN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RXDATA_BURST_LEN` writer - Configures SLC0 slave to host channel AHB burst type."]
pub type SDIO_SLC0_RXDATA_BURST_LEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_TXDATA_BURST_LEN` reader - Configures SLC1 host to slave channel AHB burst type."]
pub type SDIO_SLC1_TXDATA_BURST_LEN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_TXDATA_BURST_LEN` writer - Configures SLC1 host to slave channel AHB burst type."]
pub type SDIO_SLC1_TXDATA_BURST_LEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RXDATA_BURST_LEN` reader - Configures SLC1 slave to host channel AHB burst type."]
pub type SDIO_SLC1_RXDATA_BURST_LEN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RXDATA_BURST_LEN` writer - Configures SLC1 slave to host channel AHB burst type."]
pub type SDIO_SLC1_RXDATA_BURST_LEN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Configures SLC0 host to slave channel AHB burst type."]
    #[inline(always)]
    pub fn sdio_slc0_txdata_burst_len(&self) -> SDIO_SLC0_TXDATA_BURST_LEN_R {
        SDIO_SLC0_TXDATA_BURST_LEN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Configures SLC0 slave to host channel AHB burst type."]
    #[inline(always)]
    pub fn sdio_slc0_rxdata_burst_len(&self) -> SDIO_SLC0_RXDATA_BURST_LEN_R {
        SDIO_SLC0_RXDATA_BURST_LEN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Configures SLC1 host to slave channel AHB burst type."]
    #[inline(always)]
    pub fn sdio_slc1_txdata_burst_len(&self) -> SDIO_SLC1_TXDATA_BURST_LEN_R {
        SDIO_SLC1_TXDATA_BURST_LEN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Configures SLC1 slave to host channel AHB burst type."]
    #[inline(always)]
    pub fn sdio_slc1_rxdata_burst_len(&self) -> SDIO_SLC1_RXDATA_BURST_LEN_R {
        SDIO_SLC1_RXDATA_BURST_LEN_R::new(((self.bits >> 3) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC_BURST_LEN")
            .field(
                "sdio_slc0_txdata_burst_len",
                &self.sdio_slc0_txdata_burst_len(),
            )
            .field(
                "sdio_slc0_rxdata_burst_len",
                &self.sdio_slc0_rxdata_burst_len(),
            )
            .field(
                "sdio_slc1_txdata_burst_len",
                &self.sdio_slc1_txdata_burst_len(),
            )
            .field(
                "sdio_slc1_rxdata_burst_len",
                &self.sdio_slc1_rxdata_burst_len(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Configures SLC0 host to slave channel AHB burst type."]
    #[inline(always)]
    pub fn sdio_slc0_txdata_burst_len(
        &mut self,
    ) -> SDIO_SLC0_TXDATA_BURST_LEN_W<'_, SLC_BURST_LEN_SPEC> {
        SDIO_SLC0_TXDATA_BURST_LEN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Configures SLC0 slave to host channel AHB burst type."]
    #[inline(always)]
    pub fn sdio_slc0_rxdata_burst_len(
        &mut self,
    ) -> SDIO_SLC0_RXDATA_BURST_LEN_W<'_, SLC_BURST_LEN_SPEC> {
        SDIO_SLC0_RXDATA_BURST_LEN_W::new(self, 1)
    }
    #[doc = "Bit 2 - Configures SLC1 host to slave channel AHB burst type."]
    #[inline(always)]
    pub fn sdio_slc1_txdata_burst_len(
        &mut self,
    ) -> SDIO_SLC1_TXDATA_BURST_LEN_W<'_, SLC_BURST_LEN_SPEC> {
        SDIO_SLC1_TXDATA_BURST_LEN_W::new(self, 2)
    }
    #[doc = "Bit 3 - Configures SLC1 slave to host channel AHB burst type."]
    #[inline(always)]
    pub fn sdio_slc1_rxdata_burst_len(
        &mut self,
    ) -> SDIO_SLC1_RXDATA_BURST_LEN_W<'_, SLC_BURST_LEN_SPEC> {
        SDIO_SLC1_RXDATA_BURST_LEN_W::new(self, 3)
    }
}
#[doc = "DMA AHB burst type configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slc_burst_len::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc_burst_len::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC_BURST_LEN_SPEC;
impl crate::RegisterSpec for SLC_BURST_LEN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc_burst_len::R`](R) reader structure"]
impl crate::Readable for SLC_BURST_LEN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slc_burst_len::W`](W) writer structure"]
impl crate::Writable for SLC_BURST_LEN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC_BURST_LEN to value 0x0f"]
impl crate::Resettable for SLC_BURST_LEN_SPEC {
    const RESET_VALUE: u32 = 0x0f;
}
