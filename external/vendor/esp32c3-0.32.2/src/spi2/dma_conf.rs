#[doc = "Register `DMA_CONF` reader"]
pub type R = crate::R<DMA_CONF_SPEC>;
#[doc = "Register `DMA_CONF` writer"]
pub type W = crate::W<DMA_CONF_SPEC>;
#[doc = "Field `DMA_SLV_SEG_TRANS_EN` reader - Enable dma segment transfer in spi dma half slave mode. 1: enable. 0: disable."]
pub type DMA_SLV_SEG_TRANS_EN_R = crate::BitReader;
#[doc = "Field `DMA_SLV_SEG_TRANS_EN` writer - Enable dma segment transfer in spi dma half slave mode. 1: enable. 0: disable."]
pub type DMA_SLV_SEG_TRANS_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_RX_SEG_TRANS_CLR_EN` reader - 1: spi_dma_infifo_full_vld is cleared by spi slave cmd 5. 0: spi_dma_infifo_full_vld is cleared by spi_trans_done."]
pub type SLV_RX_SEG_TRANS_CLR_EN_R = crate::BitReader;
#[doc = "Field `SLV_RX_SEG_TRANS_CLR_EN` writer - 1: spi_dma_infifo_full_vld is cleared by spi slave cmd 5. 0: spi_dma_infifo_full_vld is cleared by spi_trans_done."]
pub type SLV_RX_SEG_TRANS_CLR_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_TX_SEG_TRANS_CLR_EN` reader - 1: spi_dma_outfifo_empty_vld is cleared by spi slave cmd 6. 0: spi_dma_outfifo_empty_vld is cleared by spi_trans_done."]
pub type SLV_TX_SEG_TRANS_CLR_EN_R = crate::BitReader;
#[doc = "Field `SLV_TX_SEG_TRANS_CLR_EN` writer - 1: spi_dma_outfifo_empty_vld is cleared by spi slave cmd 6. 0: spi_dma_outfifo_empty_vld is cleared by spi_trans_done."]
pub type SLV_TX_SEG_TRANS_CLR_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_EOF_EN` reader - 1: spi_dma_inlink_eof is set when the number of dma pushed data bytes is equal to the value of spi_slv/mst_dma_rd_bytelen\\[19:0\\] in spi dma transition. 0: spi_dma_inlink_eof is set by spi_trans_done in non-seg-trans or spi_dma_seg_trans_done in seg-trans."]
pub type RX_EOF_EN_R = crate::BitReader;
#[doc = "Field `RX_EOF_EN` writer - 1: spi_dma_inlink_eof is set when the number of dma pushed data bytes is equal to the value of spi_slv/mst_dma_rd_bytelen\\[19:0\\] in spi dma transition. 0: spi_dma_inlink_eof is set by spi_trans_done in non-seg-trans or spi_dma_seg_trans_done in seg-trans."]
pub type RX_EOF_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DMA_RX_ENA` reader - Set this bit to enable SPI DMA controlled receive data mode."]
pub type DMA_RX_ENA_R = crate::BitReader;
#[doc = "Field `DMA_RX_ENA` writer - Set this bit to enable SPI DMA controlled receive data mode."]
pub type DMA_RX_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DMA_TX_ENA` reader - Set this bit to enable SPI DMA controlled send data mode."]
pub type DMA_TX_ENA_R = crate::BitReader;
#[doc = "Field `DMA_TX_ENA` writer - Set this bit to enable SPI DMA controlled send data mode."]
pub type DMA_TX_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_AFIFO_RST` writer - Set this bit to reset RX AFIFO, which is used to receive data in SPI master and slave mode transfer."]
pub type RX_AFIFO_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BUF_AFIFO_RST` writer - Set this bit to reset BUF TX AFIFO, which is used send data out in SPI slave CPU controlled mode transfer and master mode transfer."]
pub type BUF_AFIFO_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DMA_AFIFO_RST` writer - Set this bit to reset DMA TX AFIFO, which is used to send data out in SPI slave DMA controlled mode transfer."]
pub type DMA_AFIFO_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 18 - Enable dma segment transfer in spi dma half slave mode. 1: enable. 0: disable."]
    #[inline(always)]
    pub fn dma_slv_seg_trans_en(&self) -> DMA_SLV_SEG_TRANS_EN_R {
        DMA_SLV_SEG_TRANS_EN_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - 1: spi_dma_infifo_full_vld is cleared by spi slave cmd 5. 0: spi_dma_infifo_full_vld is cleared by spi_trans_done."]
    #[inline(always)]
    pub fn slv_rx_seg_trans_clr_en(&self) -> SLV_RX_SEG_TRANS_CLR_EN_R {
        SLV_RX_SEG_TRANS_CLR_EN_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - 1: spi_dma_outfifo_empty_vld is cleared by spi slave cmd 6. 0: spi_dma_outfifo_empty_vld is cleared by spi_trans_done."]
    #[inline(always)]
    pub fn slv_tx_seg_trans_clr_en(&self) -> SLV_TX_SEG_TRANS_CLR_EN_R {
        SLV_TX_SEG_TRANS_CLR_EN_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - 1: spi_dma_inlink_eof is set when the number of dma pushed data bytes is equal to the value of spi_slv/mst_dma_rd_bytelen\\[19:0\\] in spi dma transition. 0: spi_dma_inlink_eof is set by spi_trans_done in non-seg-trans or spi_dma_seg_trans_done in seg-trans."]
    #[inline(always)]
    pub fn rx_eof_en(&self) -> RX_EOF_EN_R {
        RX_EOF_EN_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 27 - Set this bit to enable SPI DMA controlled receive data mode."]
    #[inline(always)]
    pub fn dma_rx_ena(&self) -> DMA_RX_ENA_R {
        DMA_RX_ENA_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - Set this bit to enable SPI DMA controlled send data mode."]
    #[inline(always)]
    pub fn dma_tx_ena(&self) -> DMA_TX_ENA_R {
        DMA_TX_ENA_R::new(((self.bits >> 28) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DMA_CONF")
            .field("dma_slv_seg_trans_en", &self.dma_slv_seg_trans_en())
            .field("slv_rx_seg_trans_clr_en", &self.slv_rx_seg_trans_clr_en())
            .field("slv_tx_seg_trans_clr_en", &self.slv_tx_seg_trans_clr_en())
            .field("rx_eof_en", &self.rx_eof_en())
            .field("dma_rx_ena", &self.dma_rx_ena())
            .field("dma_tx_ena", &self.dma_tx_ena())
            .finish()
    }
}
impl W {
    #[doc = "Bit 18 - Enable dma segment transfer in spi dma half slave mode. 1: enable. 0: disable."]
    #[inline(always)]
    pub fn dma_slv_seg_trans_en(&mut self) -> DMA_SLV_SEG_TRANS_EN_W<'_, DMA_CONF_SPEC> {
        DMA_SLV_SEG_TRANS_EN_W::new(self, 18)
    }
    #[doc = "Bit 19 - 1: spi_dma_infifo_full_vld is cleared by spi slave cmd 5. 0: spi_dma_infifo_full_vld is cleared by spi_trans_done."]
    #[inline(always)]
    pub fn slv_rx_seg_trans_clr_en(&mut self) -> SLV_RX_SEG_TRANS_CLR_EN_W<'_, DMA_CONF_SPEC> {
        SLV_RX_SEG_TRANS_CLR_EN_W::new(self, 19)
    }
    #[doc = "Bit 20 - 1: spi_dma_outfifo_empty_vld is cleared by spi slave cmd 6. 0: spi_dma_outfifo_empty_vld is cleared by spi_trans_done."]
    #[inline(always)]
    pub fn slv_tx_seg_trans_clr_en(&mut self) -> SLV_TX_SEG_TRANS_CLR_EN_W<'_, DMA_CONF_SPEC> {
        SLV_TX_SEG_TRANS_CLR_EN_W::new(self, 20)
    }
    #[doc = "Bit 21 - 1: spi_dma_inlink_eof is set when the number of dma pushed data bytes is equal to the value of spi_slv/mst_dma_rd_bytelen\\[19:0\\] in spi dma transition. 0: spi_dma_inlink_eof is set by spi_trans_done in non-seg-trans or spi_dma_seg_trans_done in seg-trans."]
    #[inline(always)]
    pub fn rx_eof_en(&mut self) -> RX_EOF_EN_W<'_, DMA_CONF_SPEC> {
        RX_EOF_EN_W::new(self, 21)
    }
    #[doc = "Bit 27 - Set this bit to enable SPI DMA controlled receive data mode."]
    #[inline(always)]
    pub fn dma_rx_ena(&mut self) -> DMA_RX_ENA_W<'_, DMA_CONF_SPEC> {
        DMA_RX_ENA_W::new(self, 27)
    }
    #[doc = "Bit 28 - Set this bit to enable SPI DMA controlled send data mode."]
    #[inline(always)]
    pub fn dma_tx_ena(&mut self) -> DMA_TX_ENA_W<'_, DMA_CONF_SPEC> {
        DMA_TX_ENA_W::new(self, 28)
    }
    #[doc = "Bit 29 - Set this bit to reset RX AFIFO, which is used to receive data in SPI master and slave mode transfer."]
    #[inline(always)]
    pub fn rx_afifo_rst(&mut self) -> RX_AFIFO_RST_W<'_, DMA_CONF_SPEC> {
        RX_AFIFO_RST_W::new(self, 29)
    }
    #[doc = "Bit 30 - Set this bit to reset BUF TX AFIFO, which is used send data out in SPI slave CPU controlled mode transfer and master mode transfer."]
    #[inline(always)]
    pub fn buf_afifo_rst(&mut self) -> BUF_AFIFO_RST_W<'_, DMA_CONF_SPEC> {
        BUF_AFIFO_RST_W::new(self, 30)
    }
    #[doc = "Bit 31 - Set this bit to reset DMA TX AFIFO, which is used to send data out in SPI slave DMA controlled mode transfer."]
    #[inline(always)]
    pub fn dma_afifo_rst(&mut self) -> DMA_AFIFO_RST_W<'_, DMA_CONF_SPEC> {
        DMA_AFIFO_RST_W::new(self, 31)
    }
}
#[doc = "SPI DMA control register\n\nYou can [`read`](crate::Reg::read) this register and get [`dma_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DMA_CONF_SPEC;
impl crate::RegisterSpec for DMA_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_conf::R`](R) reader structure"]
impl crate::Readable for DMA_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dma_conf::W`](W) writer structure"]
impl crate::Writable for DMA_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DMA_CONF to value 0"]
impl crate::Resettable for DMA_CONF_SPEC {}
