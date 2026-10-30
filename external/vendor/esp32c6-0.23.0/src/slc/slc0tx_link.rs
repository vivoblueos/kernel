#[doc = "Register `SLC0TX_LINK` reader"]
pub type R = crate::R<SLC0TX_LINK_SPEC>;
#[doc = "Register `SLC0TX_LINK` writer"]
pub type W = crate::W<SLC0TX_LINK_SPEC>;
#[doc = "Field `SDIO_SLC0_TXLINK_STOP` reader - Configures whether to stop SLC0 TX linked list operation."]
pub type SDIO_SLC0_TXLINK_STOP_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TXLINK_STOP` writer - Configures whether to stop SLC0 TX linked list operation."]
pub type SDIO_SLC0_TXLINK_STOP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TXLINK_START` reader - Configures whether to start SLC0 TX linked list operation from the address indicated by SDIO_SLC0_TXLINK_ADDR."]
pub type SDIO_SLC0_TXLINK_START_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TXLINK_START` writer - Configures whether to start SLC0 TX linked list operation from the address indicated by SDIO_SLC0_TXLINK_ADDR."]
pub type SDIO_SLC0_TXLINK_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TXLINK_RESTART` reader - Configures whether to restart and continue SLC0 TX linked list operation."]
pub type SDIO_SLC0_TXLINK_RESTART_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TXLINK_RESTART` writer - Configures whether to restart and continue SLC0 TX linked list operation."]
pub type SDIO_SLC0_TXLINK_RESTART_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TXLINK_PARK` reader - Represents SLC0 TX linked list FSM state."]
pub type SDIO_SLC0_TXLINK_PARK_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TXLINK_PARK` writer - Represents SLC0 TX linked list FSM state."]
pub type SDIO_SLC0_TXLINK_PARK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 28 - Configures whether to stop SLC0 TX linked list operation."]
    #[inline(always)]
    pub fn sdio_slc0_txlink_stop(&self) -> SDIO_SLC0_TXLINK_STOP_R {
        SDIO_SLC0_TXLINK_STOP_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - Configures whether to start SLC0 TX linked list operation from the address indicated by SDIO_SLC0_TXLINK_ADDR."]
    #[inline(always)]
    pub fn sdio_slc0_txlink_start(&self) -> SDIO_SLC0_TXLINK_START_R {
        SDIO_SLC0_TXLINK_START_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - Configures whether to restart and continue SLC0 TX linked list operation."]
    #[inline(always)]
    pub fn sdio_slc0_txlink_restart(&self) -> SDIO_SLC0_TXLINK_RESTART_R {
        SDIO_SLC0_TXLINK_RESTART_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Represents SLC0 TX linked list FSM state."]
    #[inline(always)]
    pub fn sdio_slc0_txlink_park(&self) -> SDIO_SLC0_TXLINK_PARK_R {
        SDIO_SLC0_TXLINK_PARK_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC0TX_LINK")
            .field("sdio_slc0_txlink_stop", &self.sdio_slc0_txlink_stop())
            .field("sdio_slc0_txlink_start", &self.sdio_slc0_txlink_start())
            .field("sdio_slc0_txlink_restart", &self.sdio_slc0_txlink_restart())
            .field("sdio_slc0_txlink_park", &self.sdio_slc0_txlink_park())
            .finish()
    }
}
impl W {
    #[doc = "Bit 28 - Configures whether to stop SLC0 TX linked list operation."]
    #[inline(always)]
    pub fn sdio_slc0_txlink_stop(&mut self) -> SDIO_SLC0_TXLINK_STOP_W<'_, SLC0TX_LINK_SPEC> {
        SDIO_SLC0_TXLINK_STOP_W::new(self, 28)
    }
    #[doc = "Bit 29 - Configures whether to start SLC0 TX linked list operation from the address indicated by SDIO_SLC0_TXLINK_ADDR."]
    #[inline(always)]
    pub fn sdio_slc0_txlink_start(&mut self) -> SDIO_SLC0_TXLINK_START_W<'_, SLC0TX_LINK_SPEC> {
        SDIO_SLC0_TXLINK_START_W::new(self, 29)
    }
    #[doc = "Bit 30 - Configures whether to restart and continue SLC0 TX linked list operation."]
    #[inline(always)]
    pub fn sdio_slc0_txlink_restart(&mut self) -> SDIO_SLC0_TXLINK_RESTART_W<'_, SLC0TX_LINK_SPEC> {
        SDIO_SLC0_TXLINK_RESTART_W::new(self, 30)
    }
    #[doc = "Bit 31 - Represents SLC0 TX linked list FSM state."]
    #[inline(always)]
    pub fn sdio_slc0_txlink_park(&mut self) -> SDIO_SLC0_TXLINK_PARK_W<'_, SLC0TX_LINK_SPEC> {
        SDIO_SLC0_TXLINK_PARK_W::new(self, 31)
    }
}
#[doc = "SLC0 TX linked list configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0tx_link::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0tx_link::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC0TX_LINK_SPEC;
impl crate::RegisterSpec for SLC0TX_LINK_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc0tx_link::R`](R) reader structure"]
impl crate::Readable for SLC0TX_LINK_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slc0tx_link::W`](W) writer structure"]
impl crate::Writable for SLC0TX_LINK_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC0TX_LINK to value 0x8000_0000"]
impl crate::Resettable for SLC0TX_LINK_SPEC {
    const RESET_VALUE: u32 = 0x8000_0000;
}
