#[doc = "Register `SLCCONF0` reader"]
pub type R = crate::R<SLCCONF0_SPEC>;
#[doc = "Register `SLCCONF0` writer"]
pub type W = crate::W<SLCCONF0_SPEC>;
#[doc = "Field `SDIO_SLC0_TX_RST` reader - Configures whether to reset TX (host to slave) FSM (finite state machine) in SLC0."]
pub type SDIO_SLC0_TX_RST_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_RST` writer - Configures whether to reset TX (host to slave) FSM (finite state machine) in SLC0."]
pub type SDIO_SLC0_TX_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_RST` reader - Configures whether to reset RX (slave to host) FSM in SCL0."]
pub type SDIO_SLC0_RX_RST_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_RST` writer - Configures whether to reset RX (slave to host) FSM in SCL0."]
pub type SDIO_SLC0_RX_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TX_LOOP_TEST` reader - Configures whether SCL0 loops around when the slave buffer finishes receiving packets from the host."]
pub type SDIO_SLC0_TX_LOOP_TEST_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_LOOP_TEST` writer - Configures whether SCL0 loops around when the slave buffer finishes receiving packets from the host."]
pub type SDIO_SLC0_TX_LOOP_TEST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_LOOP_TEST` reader - Configures whether SCL0 loops around when the slave buffer finishes sending packets to the host."]
pub type SDIO_SLC0_RX_LOOP_TEST_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_LOOP_TEST` writer - Configures whether SCL0 loops around when the slave buffer finishes sending packets to the host."]
pub type SDIO_SLC0_RX_LOOP_TEST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_AUTO_WRBACK` reader - Configures whether SCL0 changes the owner bit of RX linked list."]
pub type SDIO_SLC0_RX_AUTO_WRBACK_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_AUTO_WRBACK` writer - Configures whether SCL0 changes the owner bit of RX linked list."]
pub type SDIO_SLC0_RX_AUTO_WRBACK_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_NO_RESTART_CLR` reader - Please initialize to 1, and do not modify it."]
pub type SDIO_SLC0_RX_NO_RESTART_CLR_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_NO_RESTART_CLR` writer - Please initialize to 1, and do not modify it."]
pub type SDIO_SLC0_RX_NO_RESTART_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RXDSCR_BURST_EN` reader - Configures whether SCL0 can use AHB burst operation when reading the RX linked list from memory."]
pub type SDIO_SLC0_RXDSCR_BURST_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RXDSCR_BURST_EN` writer - Configures whether SCL0 can use AHB burst operation when reading the RX linked list from memory."]
pub type SDIO_SLC0_RXDSCR_BURST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RXDATA_BURST_EN` reader - Configures whether SCL0 can use AHB burst operation when read data from memory."]
pub type SDIO_SLC0_RXDATA_BURST_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RXDATA_BURST_EN` writer - Configures whether SCL0 can use AHB burst operation when read data from memory."]
pub type SDIO_SLC0_RXDATA_BURST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TXDSCR_BURST_EN` reader - Configures whether SCL0 can use AHB burst operation when read the TX linked list from memory."]
pub type SDIO_SLC0_TXDSCR_BURST_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TXDSCR_BURST_EN` writer - Configures whether SCL0 can use AHB burst operation when read the TX linked list from memory."]
pub type SDIO_SLC0_TXDSCR_BURST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TXDATA_BURST_EN` reader - Configures whether SCL0 can use AHB burst operation when send data to memory."]
pub type SDIO_SLC0_TXDATA_BURST_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TXDATA_BURST_EN` writer - Configures whether SCL0 can use AHB burst operation when send data to memory."]
pub type SDIO_SLC0_TXDATA_BURST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TOKEN_AUTO_CLR` reader - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC0_TOKEN_AUTO_CLR_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TOKEN_AUTO_CLR` writer - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC0_TOKEN_AUTO_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_TX_RST` reader - Configures whether to reset TX FSM in SLC1."]
pub type SDIO_SLC1_TX_RST_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_TX_RST` writer - Configures whether to reset TX FSM in SLC1."]
pub type SDIO_SLC1_TX_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RX_RST` reader - Configures whether to reset RX FSM in SLC1."]
pub type SDIO_SLC1_RX_RST_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RX_RST` writer - Configures whether to reset RX FSM in SLC1."]
pub type SDIO_SLC1_RX_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_TX_LOOP_TEST` reader - Configures whether SCL1 loops around when the slave buffer finishes receiving packets from the host."]
pub type SDIO_SLC1_TX_LOOP_TEST_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_TX_LOOP_TEST` writer - Configures whether SCL1 loops around when the slave buffer finishes receiving packets from the host."]
pub type SDIO_SLC1_TX_LOOP_TEST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RX_LOOP_TEST` reader - Configures whether SCL1 loops around when the slave buffer finishes sending packets to the host."]
pub type SDIO_SLC1_RX_LOOP_TEST_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RX_LOOP_TEST` writer - Configures whether SCL1 loops around when the slave buffer finishes sending packets to the host."]
pub type SDIO_SLC1_RX_LOOP_TEST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RX_AUTO_WRBACK` reader - Configures whether SCL1 changes the owner bit of the RX linked list."]
pub type SDIO_SLC1_RX_AUTO_WRBACK_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RX_AUTO_WRBACK` writer - Configures whether SCL1 changes the owner bit of the RX linked list."]
pub type SDIO_SLC1_RX_AUTO_WRBACK_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RX_NO_RESTART_CLR` reader - Please initialize to 1, and do not modify it."]
pub type SDIO_SLC1_RX_NO_RESTART_CLR_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RX_NO_RESTART_CLR` writer - Please initialize to 1, and do not modify it."]
pub type SDIO_SLC1_RX_NO_RESTART_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RXDSCR_BURST_EN` reader - Configures whether SCL1 can use AHB burst operation when read the RX linked list from memory."]
pub type SDIO_SLC1_RXDSCR_BURST_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RXDSCR_BURST_EN` writer - Configures whether SCL1 can use AHB burst operation when read the RX linked list from memory."]
pub type SDIO_SLC1_RXDSCR_BURST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RXDATA_BURST_EN` reader - Configures whether SCL1 can use AHB burst operation when reading data from memory."]
pub type SDIO_SLC1_RXDATA_BURST_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RXDATA_BURST_EN` writer - Configures whether SCL1 can use AHB burst operation when reading data from memory."]
pub type SDIO_SLC1_RXDATA_BURST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_TXDSCR_BURST_EN` reader - Configures whether SCL1 can use AHB burst operation when read the TX linked list from memory."]
pub type SDIO_SLC1_TXDSCR_BURST_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_TXDSCR_BURST_EN` writer - Configures whether SCL1 can use AHB burst operation when read the TX linked list from memory."]
pub type SDIO_SLC1_TXDSCR_BURST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_TXDATA_BURST_EN` reader - Configures whether SCL1 can use AHB burst operation when send data to memory."]
pub type SDIO_SLC1_TXDATA_BURST_EN_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_TXDATA_BURST_EN` writer - Configures whether SCL1 can use AHB burst operation when send data to memory."]
pub type SDIO_SLC1_TXDATA_BURST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_TOKEN_AUTO_CLR` reader - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC1_TOKEN_AUTO_CLR_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_TOKEN_AUTO_CLR` writer - Please initialize to 0, and do not modify it."]
pub type SDIO_SLC1_TOKEN_AUTO_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Configures whether to reset TX (host to slave) FSM (finite state machine) in SLC0."]
    #[inline(always)]
    pub fn sdio_slc0_tx_rst(&self) -> SDIO_SLC0_TX_RST_R {
        SDIO_SLC0_TX_RST_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Configures whether to reset RX (slave to host) FSM in SCL0."]
    #[inline(always)]
    pub fn sdio_slc0_rx_rst(&self) -> SDIO_SLC0_RX_RST_R {
        SDIO_SLC0_RX_RST_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 4 - Configures whether SCL0 loops around when the slave buffer finishes receiving packets from the host."]
    #[inline(always)]
    pub fn sdio_slc0_tx_loop_test(&self) -> SDIO_SLC0_TX_LOOP_TEST_R {
        SDIO_SLC0_TX_LOOP_TEST_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Configures whether SCL0 loops around when the slave buffer finishes sending packets to the host."]
    #[inline(always)]
    pub fn sdio_slc0_rx_loop_test(&self) -> SDIO_SLC0_RX_LOOP_TEST_R {
        SDIO_SLC0_RX_LOOP_TEST_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Configures whether SCL0 changes the owner bit of RX linked list."]
    #[inline(always)]
    pub fn sdio_slc0_rx_auto_wrback(&self) -> SDIO_SLC0_RX_AUTO_WRBACK_R {
        SDIO_SLC0_RX_AUTO_WRBACK_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Please initialize to 1, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc0_rx_no_restart_clr(&self) -> SDIO_SLC0_RX_NO_RESTART_CLR_R {
        SDIO_SLC0_RX_NO_RESTART_CLR_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Configures whether SCL0 can use AHB burst operation when reading the RX linked list from memory."]
    #[inline(always)]
    pub fn sdio_slc0_rxdscr_burst_en(&self) -> SDIO_SLC0_RXDSCR_BURST_EN_R {
        SDIO_SLC0_RXDSCR_BURST_EN_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Configures whether SCL0 can use AHB burst operation when read data from memory."]
    #[inline(always)]
    pub fn sdio_slc0_rxdata_burst_en(&self) -> SDIO_SLC0_RXDATA_BURST_EN_R {
        SDIO_SLC0_RXDATA_BURST_EN_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 12 - Configures whether SCL0 can use AHB burst operation when read the TX linked list from memory."]
    #[inline(always)]
    pub fn sdio_slc0_txdscr_burst_en(&self) -> SDIO_SLC0_TXDSCR_BURST_EN_R {
        SDIO_SLC0_TXDSCR_BURST_EN_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Configures whether SCL0 can use AHB burst operation when send data to memory."]
    #[inline(always)]
    pub fn sdio_slc0_txdata_burst_en(&self) -> SDIO_SLC0_TXDATA_BURST_EN_R {
        SDIO_SLC0_TXDATA_BURST_EN_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc0_token_auto_clr(&self) -> SDIO_SLC0_TOKEN_AUTO_CLR_R {
        SDIO_SLC0_TOKEN_AUTO_CLR_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 16 - Configures whether to reset TX FSM in SLC1."]
    #[inline(always)]
    pub fn sdio_slc1_tx_rst(&self) -> SDIO_SLC1_TX_RST_R {
        SDIO_SLC1_TX_RST_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Configures whether to reset RX FSM in SLC1."]
    #[inline(always)]
    pub fn sdio_slc1_rx_rst(&self) -> SDIO_SLC1_RX_RST_R {
        SDIO_SLC1_RX_RST_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 20 - Configures whether SCL1 loops around when the slave buffer finishes receiving packets from the host."]
    #[inline(always)]
    pub fn sdio_slc1_tx_loop_test(&self) -> SDIO_SLC1_TX_LOOP_TEST_R {
        SDIO_SLC1_TX_LOOP_TEST_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Configures whether SCL1 loops around when the slave buffer finishes sending packets to the host."]
    #[inline(always)]
    pub fn sdio_slc1_rx_loop_test(&self) -> SDIO_SLC1_RX_LOOP_TEST_R {
        SDIO_SLC1_RX_LOOP_TEST_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - Configures whether SCL1 changes the owner bit of the RX linked list."]
    #[inline(always)]
    pub fn sdio_slc1_rx_auto_wrback(&self) -> SDIO_SLC1_RX_AUTO_WRBACK_R {
        SDIO_SLC1_RX_AUTO_WRBACK_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - Please initialize to 1, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc1_rx_no_restart_clr(&self) -> SDIO_SLC1_RX_NO_RESTART_CLR_R {
        SDIO_SLC1_RX_NO_RESTART_CLR_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - Configures whether SCL1 can use AHB burst operation when read the RX linked list from memory."]
    #[inline(always)]
    pub fn sdio_slc1_rxdscr_burst_en(&self) -> SDIO_SLC1_RXDSCR_BURST_EN_R {
        SDIO_SLC1_RXDSCR_BURST_EN_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Configures whether SCL1 can use AHB burst operation when reading data from memory."]
    #[inline(always)]
    pub fn sdio_slc1_rxdata_burst_en(&self) -> SDIO_SLC1_RXDATA_BURST_EN_R {
        SDIO_SLC1_RXDATA_BURST_EN_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 28 - Configures whether SCL1 can use AHB burst operation when read the TX linked list from memory."]
    #[inline(always)]
    pub fn sdio_slc1_txdscr_burst_en(&self) -> SDIO_SLC1_TXDSCR_BURST_EN_R {
        SDIO_SLC1_TXDSCR_BURST_EN_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - Configures whether SCL1 can use AHB burst operation when send data to memory."]
    #[inline(always)]
    pub fn sdio_slc1_txdata_burst_en(&self) -> SDIO_SLC1_TXDATA_BURST_EN_R {
        SDIO_SLC1_TXDATA_BURST_EN_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc1_token_auto_clr(&self) -> SDIO_SLC1_TOKEN_AUTO_CLR_R {
        SDIO_SLC1_TOKEN_AUTO_CLR_R::new(((self.bits >> 30) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLCCONF0")
            .field("sdio_slc0_tx_rst", &self.sdio_slc0_tx_rst())
            .field("sdio_slc0_rx_rst", &self.sdio_slc0_rx_rst())
            .field("sdio_slc0_tx_loop_test", &self.sdio_slc0_tx_loop_test())
            .field("sdio_slc0_rx_loop_test", &self.sdio_slc0_rx_loop_test())
            .field("sdio_slc0_rx_auto_wrback", &self.sdio_slc0_rx_auto_wrback())
            .field(
                "sdio_slc0_rx_no_restart_clr",
                &self.sdio_slc0_rx_no_restart_clr(),
            )
            .field(
                "sdio_slc0_rxdscr_burst_en",
                &self.sdio_slc0_rxdscr_burst_en(),
            )
            .field(
                "sdio_slc0_rxdata_burst_en",
                &self.sdio_slc0_rxdata_burst_en(),
            )
            .field(
                "sdio_slc0_txdscr_burst_en",
                &self.sdio_slc0_txdscr_burst_en(),
            )
            .field(
                "sdio_slc0_txdata_burst_en",
                &self.sdio_slc0_txdata_burst_en(),
            )
            .field("sdio_slc0_token_auto_clr", &self.sdio_slc0_token_auto_clr())
            .field("sdio_slc1_tx_rst", &self.sdio_slc1_tx_rst())
            .field("sdio_slc1_rx_rst", &self.sdio_slc1_rx_rst())
            .field("sdio_slc1_tx_loop_test", &self.sdio_slc1_tx_loop_test())
            .field("sdio_slc1_rx_loop_test", &self.sdio_slc1_rx_loop_test())
            .field("sdio_slc1_rx_auto_wrback", &self.sdio_slc1_rx_auto_wrback())
            .field(
                "sdio_slc1_rx_no_restart_clr",
                &self.sdio_slc1_rx_no_restart_clr(),
            )
            .field(
                "sdio_slc1_rxdscr_burst_en",
                &self.sdio_slc1_rxdscr_burst_en(),
            )
            .field(
                "sdio_slc1_rxdata_burst_en",
                &self.sdio_slc1_rxdata_burst_en(),
            )
            .field(
                "sdio_slc1_txdscr_burst_en",
                &self.sdio_slc1_txdscr_burst_en(),
            )
            .field(
                "sdio_slc1_txdata_burst_en",
                &self.sdio_slc1_txdata_burst_en(),
            )
            .field("sdio_slc1_token_auto_clr", &self.sdio_slc1_token_auto_clr())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Configures whether to reset TX (host to slave) FSM (finite state machine) in SLC0."]
    #[inline(always)]
    pub fn sdio_slc0_tx_rst(&mut self) -> SDIO_SLC0_TX_RST_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC0_TX_RST_W::new(self, 0)
    }
    #[doc = "Bit 1 - Configures whether to reset RX (slave to host) FSM in SCL0."]
    #[inline(always)]
    pub fn sdio_slc0_rx_rst(&mut self) -> SDIO_SLC0_RX_RST_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC0_RX_RST_W::new(self, 1)
    }
    #[doc = "Bit 4 - Configures whether SCL0 loops around when the slave buffer finishes receiving packets from the host."]
    #[inline(always)]
    pub fn sdio_slc0_tx_loop_test(&mut self) -> SDIO_SLC0_TX_LOOP_TEST_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC0_TX_LOOP_TEST_W::new(self, 4)
    }
    #[doc = "Bit 5 - Configures whether SCL0 loops around when the slave buffer finishes sending packets to the host."]
    #[inline(always)]
    pub fn sdio_slc0_rx_loop_test(&mut self) -> SDIO_SLC0_RX_LOOP_TEST_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC0_RX_LOOP_TEST_W::new(self, 5)
    }
    #[doc = "Bit 6 - Configures whether SCL0 changes the owner bit of RX linked list."]
    #[inline(always)]
    pub fn sdio_slc0_rx_auto_wrback(&mut self) -> SDIO_SLC0_RX_AUTO_WRBACK_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC0_RX_AUTO_WRBACK_W::new(self, 6)
    }
    #[doc = "Bit 7 - Please initialize to 1, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc0_rx_no_restart_clr(
        &mut self,
    ) -> SDIO_SLC0_RX_NO_RESTART_CLR_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC0_RX_NO_RESTART_CLR_W::new(self, 7)
    }
    #[doc = "Bit 8 - Configures whether SCL0 can use AHB burst operation when reading the RX linked list from memory."]
    #[inline(always)]
    pub fn sdio_slc0_rxdscr_burst_en(&mut self) -> SDIO_SLC0_RXDSCR_BURST_EN_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC0_RXDSCR_BURST_EN_W::new(self, 8)
    }
    #[doc = "Bit 9 - Configures whether SCL0 can use AHB burst operation when read data from memory."]
    #[inline(always)]
    pub fn sdio_slc0_rxdata_burst_en(&mut self) -> SDIO_SLC0_RXDATA_BURST_EN_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC0_RXDATA_BURST_EN_W::new(self, 9)
    }
    #[doc = "Bit 12 - Configures whether SCL0 can use AHB burst operation when read the TX linked list from memory."]
    #[inline(always)]
    pub fn sdio_slc0_txdscr_burst_en(&mut self) -> SDIO_SLC0_TXDSCR_BURST_EN_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC0_TXDSCR_BURST_EN_W::new(self, 12)
    }
    #[doc = "Bit 13 - Configures whether SCL0 can use AHB burst operation when send data to memory."]
    #[inline(always)]
    pub fn sdio_slc0_txdata_burst_en(&mut self) -> SDIO_SLC0_TXDATA_BURST_EN_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC0_TXDATA_BURST_EN_W::new(self, 13)
    }
    #[doc = "Bit 14 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc0_token_auto_clr(&mut self) -> SDIO_SLC0_TOKEN_AUTO_CLR_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC0_TOKEN_AUTO_CLR_W::new(self, 14)
    }
    #[doc = "Bit 16 - Configures whether to reset TX FSM in SLC1."]
    #[inline(always)]
    pub fn sdio_slc1_tx_rst(&mut self) -> SDIO_SLC1_TX_RST_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC1_TX_RST_W::new(self, 16)
    }
    #[doc = "Bit 17 - Configures whether to reset RX FSM in SLC1."]
    #[inline(always)]
    pub fn sdio_slc1_rx_rst(&mut self) -> SDIO_SLC1_RX_RST_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC1_RX_RST_W::new(self, 17)
    }
    #[doc = "Bit 20 - Configures whether SCL1 loops around when the slave buffer finishes receiving packets from the host."]
    #[inline(always)]
    pub fn sdio_slc1_tx_loop_test(&mut self) -> SDIO_SLC1_TX_LOOP_TEST_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC1_TX_LOOP_TEST_W::new(self, 20)
    }
    #[doc = "Bit 21 - Configures whether SCL1 loops around when the slave buffer finishes sending packets to the host."]
    #[inline(always)]
    pub fn sdio_slc1_rx_loop_test(&mut self) -> SDIO_SLC1_RX_LOOP_TEST_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC1_RX_LOOP_TEST_W::new(self, 21)
    }
    #[doc = "Bit 22 - Configures whether SCL1 changes the owner bit of the RX linked list."]
    #[inline(always)]
    pub fn sdio_slc1_rx_auto_wrback(&mut self) -> SDIO_SLC1_RX_AUTO_WRBACK_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC1_RX_AUTO_WRBACK_W::new(self, 22)
    }
    #[doc = "Bit 23 - Please initialize to 1, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc1_rx_no_restart_clr(
        &mut self,
    ) -> SDIO_SLC1_RX_NO_RESTART_CLR_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC1_RX_NO_RESTART_CLR_W::new(self, 23)
    }
    #[doc = "Bit 24 - Configures whether SCL1 can use AHB burst operation when read the RX linked list from memory."]
    #[inline(always)]
    pub fn sdio_slc1_rxdscr_burst_en(&mut self) -> SDIO_SLC1_RXDSCR_BURST_EN_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC1_RXDSCR_BURST_EN_W::new(self, 24)
    }
    #[doc = "Bit 25 - Configures whether SCL1 can use AHB burst operation when reading data from memory."]
    #[inline(always)]
    pub fn sdio_slc1_rxdata_burst_en(&mut self) -> SDIO_SLC1_RXDATA_BURST_EN_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC1_RXDATA_BURST_EN_W::new(self, 25)
    }
    #[doc = "Bit 28 - Configures whether SCL1 can use AHB burst operation when read the TX linked list from memory."]
    #[inline(always)]
    pub fn sdio_slc1_txdscr_burst_en(&mut self) -> SDIO_SLC1_TXDSCR_BURST_EN_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC1_TXDSCR_BURST_EN_W::new(self, 28)
    }
    #[doc = "Bit 29 - Configures whether SCL1 can use AHB burst operation when send data to memory."]
    #[inline(always)]
    pub fn sdio_slc1_txdata_burst_en(&mut self) -> SDIO_SLC1_TXDATA_BURST_EN_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC1_TXDATA_BURST_EN_W::new(self, 29)
    }
    #[doc = "Bit 30 - Please initialize to 0, and do not modify it."]
    #[inline(always)]
    pub fn sdio_slc1_token_auto_clr(&mut self) -> SDIO_SLC1_TOKEN_AUTO_CLR_W<'_, SLCCONF0_SPEC> {
        SDIO_SLC1_TOKEN_AUTO_CLR_W::new(self, 30)
    }
}
#[doc = "DMA configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slcconf0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slcconf0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLCCONF0_SPEC;
impl crate::RegisterSpec for SLCCONF0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slcconf0::R`](R) reader structure"]
impl crate::Readable for SLCCONF0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slcconf0::W`](W) writer structure"]
impl crate::Writable for SLCCONF0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLCCONF0 to value 0xff3c_ff00"]
impl crate::Resettable for SLCCONF0_SPEC {
    const RESET_VALUE: u32 = 0xff3c_ff00;
}
