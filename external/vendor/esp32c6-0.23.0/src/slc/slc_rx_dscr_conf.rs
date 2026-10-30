#[doc = "Register `SLC_RX_DSCR_CONF` reader"]
pub type R = crate::R<SLC_RX_DSCR_CONF_SPEC>;
#[doc = "Register `SLC_RX_DSCR_CONF` writer"]
pub type W = crate::W<SLC_RX_DSCR_CONF_SPEC>;
#[doc = "Field `SDIO_SLC0_TOKEN_NO_REPLACE` reader - Please initialize to 1, and do not modify it."]
pub type SDIO_SLC0_TOKEN_NO_REPLACE_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TOKEN_NO_REPLACE` writer - Please initialize to 1, and do not modify it."]
pub type SDIO_SLC0_TOKEN_NO_REPLACE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 1 - Please initialize to 1, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc0_token_no_replace(&self) -> SDIO_SLC0_TOKEN_NO_REPLACE_R {
        SDIO_SLC0_TOKEN_NO_REPLACE_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC_RX_DSCR_CONF")
            .field(
                "sdio_slc0_token_no_replace",
                &self.sdio_slc0_token_no_replace(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 1 - Please initialize to 1, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc0_token_no_replace(
        &mut self,
    ) -> SDIO_SLC0_TOKEN_NO_REPLACE_W<'_, SLC_RX_DSCR_CONF_SPEC> {
        SDIO_SLC0_TOKEN_NO_REPLACE_W::new(self, 1)
    }
}
#[doc = "DMA slave to host configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`slc_rx_dscr_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc_rx_dscr_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC_RX_DSCR_CONF_SPEC;
impl crate::RegisterSpec for SLC_RX_DSCR_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc_rx_dscr_conf::R`](R) reader structure"]
impl crate::Readable for SLC_RX_DSCR_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slc_rx_dscr_conf::W`](W) writer structure"]
impl crate::Writable for SLC_RX_DSCR_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC_RX_DSCR_CONF to value 0x0203_701a"]
impl crate::Resettable for SLC_RX_DSCR_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0203_701a;
}
