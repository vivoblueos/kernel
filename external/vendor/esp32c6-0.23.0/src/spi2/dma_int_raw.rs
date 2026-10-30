#[doc = "Register `DMA_INT_RAW` reader"]
pub type R = crate::R<DMA_INT_RAW_SPEC>;
#[doc = "Register `DMA_INT_RAW` writer"]
pub type W = crate::W<DMA_INT_RAW_SPEC>;
#[doc = "Field `DMA_INFIFO_FULL_ERR` reader - 1: The current data rate of DMA Rx is smaller than that of SPI, which will lose the receive data. 0: Others."]
pub type DMA_INFIFO_FULL_ERR_R = crate::BitReader;
#[doc = "Field `DMA_INFIFO_FULL_ERR` writer - 1: The current data rate of DMA Rx is smaller than that of SPI, which will lose the receive data. 0: Others."]
pub type DMA_INFIFO_FULL_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DMA_OUTFIFO_EMPTY_ERR` reader - 1: The current data rate of DMA TX is smaller than that of SPI. SPI will stop in master mode and send out all 0 in slave mode. 0: Others."]
pub type DMA_OUTFIFO_EMPTY_ERR_R = crate::BitReader;
#[doc = "Field `DMA_OUTFIFO_EMPTY_ERR` writer - 1: The current data rate of DMA TX is smaller than that of SPI. SPI will stop in master mode and send out all 0 in slave mode. 0: Others."]
pub type DMA_OUTFIFO_EMPTY_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_EX_QPI` reader - The raw bit for SPI slave Ex_QPI interrupt. 1: SPI slave mode Ex_QPI transmission is ended. 0: Others."]
pub type SLV_EX_QPI_R = crate::BitReader;
#[doc = "Field `SLV_EX_QPI` writer - The raw bit for SPI slave Ex_QPI interrupt. 1: SPI slave mode Ex_QPI transmission is ended. 0: Others."]
pub type SLV_EX_QPI_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_EN_QPI` reader - The raw bit for SPI slave En_QPI interrupt. 1: SPI slave mode En_QPI transmission is ended. 0: Others."]
pub type SLV_EN_QPI_R = crate::BitReader;
#[doc = "Field `SLV_EN_QPI` writer - The raw bit for SPI slave En_QPI interrupt. 1: SPI slave mode En_QPI transmission is ended. 0: Others."]
pub type SLV_EN_QPI_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_CMD7` reader - The raw bit for SPI slave CMD7 interrupt. 1: SPI slave mode CMD7 transmission is ended. 0: Others."]
pub type SLV_CMD7_R = crate::BitReader;
#[doc = "Field `SLV_CMD7` writer - The raw bit for SPI slave CMD7 interrupt. 1: SPI slave mode CMD7 transmission is ended. 0: Others."]
pub type SLV_CMD7_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_CMD8` reader - The raw bit for SPI slave CMD8 interrupt. 1: SPI slave mode CMD8 transmission is ended. 0: Others."]
pub type SLV_CMD8_R = crate::BitReader;
#[doc = "Field `SLV_CMD8` writer - The raw bit for SPI slave CMD8 interrupt. 1: SPI slave mode CMD8 transmission is ended. 0: Others."]
pub type SLV_CMD8_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_CMD9` reader - The raw bit for SPI slave CMD9 interrupt. 1: SPI slave mode CMD9 transmission is ended. 0: Others."]
pub type SLV_CMD9_R = crate::BitReader;
#[doc = "Field `SLV_CMD9` writer - The raw bit for SPI slave CMD9 interrupt. 1: SPI slave mode CMD9 transmission is ended. 0: Others."]
pub type SLV_CMD9_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_CMDA` reader - The raw bit for SPI slave CMDA interrupt. 1: SPI slave mode CMDA transmission is ended. 0: Others."]
pub type SLV_CMDA_R = crate::BitReader;
#[doc = "Field `SLV_CMDA` writer - The raw bit for SPI slave CMDA interrupt. 1: SPI slave mode CMDA transmission is ended. 0: Others."]
pub type SLV_CMDA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_RD_DMA_DONE` reader - The raw bit for SPI_SLV_RD_DMA_DONE_INT interrupt. 1: SPI slave mode Rd_DMA transmission is ended. 0: Others."]
pub type SLV_RD_DMA_DONE_R = crate::BitReader;
#[doc = "Field `SLV_RD_DMA_DONE` writer - The raw bit for SPI_SLV_RD_DMA_DONE_INT interrupt. 1: SPI slave mode Rd_DMA transmission is ended. 0: Others."]
pub type SLV_RD_DMA_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_WR_DMA_DONE` reader - The raw bit for SPI_SLV_WR_DMA_DONE_INT interrupt. 1: SPI slave mode Wr_DMA transmission is ended. 0: Others."]
pub type SLV_WR_DMA_DONE_R = crate::BitReader;
#[doc = "Field `SLV_WR_DMA_DONE` writer - The raw bit for SPI_SLV_WR_DMA_DONE_INT interrupt. 1: SPI slave mode Wr_DMA transmission is ended. 0: Others."]
pub type SLV_WR_DMA_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_RD_BUF_DONE` reader - The raw bit for SPI_SLV_RD_BUF_DONE_INT interrupt. 1: SPI slave mode Rd_BUF transmission is ended. 0: Others."]
pub type SLV_RD_BUF_DONE_R = crate::BitReader;
#[doc = "Field `SLV_RD_BUF_DONE` writer - The raw bit for SPI_SLV_RD_BUF_DONE_INT interrupt. 1: SPI slave mode Rd_BUF transmission is ended. 0: Others."]
pub type SLV_RD_BUF_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_WR_BUF_DONE` reader - The raw bit for SPI_SLV_WR_BUF_DONE_INT interrupt. 1: SPI slave mode Wr_BUF transmission is ended. 0: Others."]
pub type SLV_WR_BUF_DONE_R = crate::BitReader;
#[doc = "Field `SLV_WR_BUF_DONE` writer - The raw bit for SPI_SLV_WR_BUF_DONE_INT interrupt. 1: SPI slave mode Wr_BUF transmission is ended. 0: Others."]
pub type SLV_WR_BUF_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TRANS_DONE` reader - The raw bit for SPI_TRANS_DONE_INT interrupt. 1: SPI master mode transmission is ended. 0: others."]
pub type TRANS_DONE_R = crate::BitReader;
#[doc = "Field `TRANS_DONE` writer - The raw bit for SPI_TRANS_DONE_INT interrupt. 1: SPI master mode transmission is ended. 0: others."]
pub type TRANS_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DMA_SEG_TRANS_DONE` reader - The raw bit for SPI_DMA_SEG_TRANS_DONE_INT interrupt. 1: spi master DMA full-duplex/half-duplex seg-conf-trans ends or slave half-duplex seg-trans ends. And data has been pushed to corresponding memory. 0: seg-conf-trans or seg-trans is not ended or not occurred."]
pub type DMA_SEG_TRANS_DONE_R = crate::BitReader;
#[doc = "Field `DMA_SEG_TRANS_DONE` writer - The raw bit for SPI_DMA_SEG_TRANS_DONE_INT interrupt. 1: spi master DMA full-duplex/half-duplex seg-conf-trans ends or slave half-duplex seg-trans ends. And data has been pushed to corresponding memory. 0: seg-conf-trans or seg-trans is not ended or not occurred."]
pub type DMA_SEG_TRANS_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SEG_MAGIC_ERR` reader - The raw bit for SPI_SEG_MAGIC_ERR_INT interrupt. 1: The magic value in CONF buffer is error in the DMA seg-conf-trans. 0: others."]
pub type SEG_MAGIC_ERR_R = crate::BitReader;
#[doc = "Field `SEG_MAGIC_ERR` writer - The raw bit for SPI_SEG_MAGIC_ERR_INT interrupt. 1: The magic value in CONF buffer is error in the DMA seg-conf-trans. 0: others."]
pub type SEG_MAGIC_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_BUF_ADDR_ERR` reader - The raw bit for SPI_SLV_BUF_ADDR_ERR_INT interrupt. 1: The accessing data address of the current SPI slave mode CPU controlled FD, Wr_BUF or Rd_BUF transmission is bigger than 63. 0: Others."]
pub type SLV_BUF_ADDR_ERR_R = crate::BitReader;
#[doc = "Field `SLV_BUF_ADDR_ERR` writer - The raw bit for SPI_SLV_BUF_ADDR_ERR_INT interrupt. 1: The accessing data address of the current SPI slave mode CPU controlled FD, Wr_BUF or Rd_BUF transmission is bigger than 63. 0: Others."]
pub type SLV_BUF_ADDR_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_CMD_ERR` reader - The raw bit for SPI_SLV_CMD_ERR_INT interrupt. 1: The slave command value in the current SPI slave HD mode transmission is not supported. 0: Others."]
pub type SLV_CMD_ERR_R = crate::BitReader;
#[doc = "Field `SLV_CMD_ERR` writer - The raw bit for SPI_SLV_CMD_ERR_INT interrupt. 1: The slave command value in the current SPI slave HD mode transmission is not supported. 0: Others."]
pub type SLV_CMD_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MST_RX_AFIFO_WFULL_ERR` reader - The raw bit for SPI_MST_RX_AFIFO_WFULL_ERR_INT interrupt. 1: There is a RX AFIFO write-full error when SPI inputs data in master mode. 0: Others."]
pub type MST_RX_AFIFO_WFULL_ERR_R = crate::BitReader;
#[doc = "Field `MST_RX_AFIFO_WFULL_ERR` writer - The raw bit for SPI_MST_RX_AFIFO_WFULL_ERR_INT interrupt. 1: There is a RX AFIFO write-full error when SPI inputs data in master mode. 0: Others."]
pub type MST_RX_AFIFO_WFULL_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MST_TX_AFIFO_REMPTY_ERR` reader - The raw bit for SPI_MST_TX_AFIFO_REMPTY_ERR_INT interrupt. 1: There is a TX BUF AFIFO read-empty error when SPI outputs data in master mode. 0: Others."]
pub type MST_TX_AFIFO_REMPTY_ERR_R = crate::BitReader;
#[doc = "Field `MST_TX_AFIFO_REMPTY_ERR` writer - The raw bit for SPI_MST_TX_AFIFO_REMPTY_ERR_INT interrupt. 1: There is a TX BUF AFIFO read-empty error when SPI outputs data in master mode. 0: Others."]
pub type MST_TX_AFIFO_REMPTY_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `APP2` reader - The raw bit for SPI_APP2_INT interrupt. The value is only controlled by software."]
pub type APP2_R = crate::BitReader;
#[doc = "Field `APP2` writer - The raw bit for SPI_APP2_INT interrupt. The value is only controlled by software."]
pub type APP2_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `APP1` reader - The raw bit for SPI_APP1_INT interrupt. The value is only controlled by software."]
pub type APP1_R = crate::BitReader;
#[doc = "Field `APP1` writer - The raw bit for SPI_APP1_INT interrupt. The value is only controlled by software."]
pub type APP1_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - 1: The current data rate of DMA Rx is smaller than that of SPI, which will lose the receive data. 0: Others."]
    #[inline(always)]
    pub fn dma_infifo_full_err(&self) -> DMA_INFIFO_FULL_ERR_R {
        DMA_INFIFO_FULL_ERR_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - 1: The current data rate of DMA TX is smaller than that of SPI. SPI will stop in master mode and send out all 0 in slave mode. 0: Others."]
    #[inline(always)]
    pub fn dma_outfifo_empty_err(&self) -> DMA_OUTFIFO_EMPTY_ERR_R {
        DMA_OUTFIFO_EMPTY_ERR_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The raw bit for SPI slave Ex_QPI interrupt. 1: SPI slave mode Ex_QPI transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_ex_qpi(&self) -> SLV_EX_QPI_R {
        SLV_EX_QPI_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The raw bit for SPI slave En_QPI interrupt. 1: SPI slave mode En_QPI transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_en_qpi(&self) -> SLV_EN_QPI_R {
        SLV_EN_QPI_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The raw bit for SPI slave CMD7 interrupt. 1: SPI slave mode CMD7 transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_cmd7(&self) -> SLV_CMD7_R {
        SLV_CMD7_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The raw bit for SPI slave CMD8 interrupt. 1: SPI slave mode CMD8 transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_cmd8(&self) -> SLV_CMD8_R {
        SLV_CMD8_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The raw bit for SPI slave CMD9 interrupt. 1: SPI slave mode CMD9 transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_cmd9(&self) -> SLV_CMD9_R {
        SLV_CMD9_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The raw bit for SPI slave CMDA interrupt. 1: SPI slave mode CMDA transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_cmda(&self) -> SLV_CMDA_R {
        SLV_CMDA_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The raw bit for SPI_SLV_RD_DMA_DONE_INT interrupt. 1: SPI slave mode Rd_DMA transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_rd_dma_done(&self) -> SLV_RD_DMA_DONE_R {
        SLV_RD_DMA_DONE_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The raw bit for SPI_SLV_WR_DMA_DONE_INT interrupt. 1: SPI slave mode Wr_DMA transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_wr_dma_done(&self) -> SLV_WR_DMA_DONE_R {
        SLV_WR_DMA_DONE_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - The raw bit for SPI_SLV_RD_BUF_DONE_INT interrupt. 1: SPI slave mode Rd_BUF transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_rd_buf_done(&self) -> SLV_RD_BUF_DONE_R {
        SLV_RD_BUF_DONE_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - The raw bit for SPI_SLV_WR_BUF_DONE_INT interrupt. 1: SPI slave mode Wr_BUF transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_wr_buf_done(&self) -> SLV_WR_BUF_DONE_R {
        SLV_WR_BUF_DONE_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - The raw bit for SPI_TRANS_DONE_INT interrupt. 1: SPI master mode transmission is ended. 0: others."]
    #[inline(always)]
    pub fn trans_done(&self) -> TRANS_DONE_R {
        TRANS_DONE_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - The raw bit for SPI_DMA_SEG_TRANS_DONE_INT interrupt. 1: spi master DMA full-duplex/half-duplex seg-conf-trans ends or slave half-duplex seg-trans ends. And data has been pushed to corresponding memory. 0: seg-conf-trans or seg-trans is not ended or not occurred."]
    #[inline(always)]
    pub fn dma_seg_trans_done(&self) -> DMA_SEG_TRANS_DONE_R {
        DMA_SEG_TRANS_DONE_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - The raw bit for SPI_SEG_MAGIC_ERR_INT interrupt. 1: The magic value in CONF buffer is error in the DMA seg-conf-trans. 0: others."]
    #[inline(always)]
    pub fn seg_magic_err(&self) -> SEG_MAGIC_ERR_R {
        SEG_MAGIC_ERR_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - The raw bit for SPI_SLV_BUF_ADDR_ERR_INT interrupt. 1: The accessing data address of the current SPI slave mode CPU controlled FD, Wr_BUF or Rd_BUF transmission is bigger than 63. 0: Others."]
    #[inline(always)]
    pub fn slv_buf_addr_err(&self) -> SLV_BUF_ADDR_ERR_R {
        SLV_BUF_ADDR_ERR_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - The raw bit for SPI_SLV_CMD_ERR_INT interrupt. 1: The slave command value in the current SPI slave HD mode transmission is not supported. 0: Others."]
    #[inline(always)]
    pub fn slv_cmd_err(&self) -> SLV_CMD_ERR_R {
        SLV_CMD_ERR_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - The raw bit for SPI_MST_RX_AFIFO_WFULL_ERR_INT interrupt. 1: There is a RX AFIFO write-full error when SPI inputs data in master mode. 0: Others."]
    #[inline(always)]
    pub fn mst_rx_afifo_wfull_err(&self) -> MST_RX_AFIFO_WFULL_ERR_R {
        MST_RX_AFIFO_WFULL_ERR_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - The raw bit for SPI_MST_TX_AFIFO_REMPTY_ERR_INT interrupt. 1: There is a TX BUF AFIFO read-empty error when SPI outputs data in master mode. 0: Others."]
    #[inline(always)]
    pub fn mst_tx_afifo_rempty_err(&self) -> MST_TX_AFIFO_REMPTY_ERR_R {
        MST_TX_AFIFO_REMPTY_ERR_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - The raw bit for SPI_APP2_INT interrupt. The value is only controlled by software."]
    #[inline(always)]
    pub fn app2(&self) -> APP2_R {
        APP2_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - The raw bit for SPI_APP1_INT interrupt. The value is only controlled by software."]
    #[inline(always)]
    pub fn app1(&self) -> APP1_R {
        APP1_R::new(((self.bits >> 20) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DMA_INT_RAW")
            .field("dma_infifo_full_err", &self.dma_infifo_full_err())
            .field("dma_outfifo_empty_err", &self.dma_outfifo_empty_err())
            .field("slv_ex_qpi", &self.slv_ex_qpi())
            .field("slv_en_qpi", &self.slv_en_qpi())
            .field("slv_cmd7", &self.slv_cmd7())
            .field("slv_cmd8", &self.slv_cmd8())
            .field("slv_cmd9", &self.slv_cmd9())
            .field("slv_cmda", &self.slv_cmda())
            .field("slv_rd_dma_done", &self.slv_rd_dma_done())
            .field("slv_wr_dma_done", &self.slv_wr_dma_done())
            .field("slv_rd_buf_done", &self.slv_rd_buf_done())
            .field("slv_wr_buf_done", &self.slv_wr_buf_done())
            .field("trans_done", &self.trans_done())
            .field("dma_seg_trans_done", &self.dma_seg_trans_done())
            .field("seg_magic_err", &self.seg_magic_err())
            .field("slv_buf_addr_err", &self.slv_buf_addr_err())
            .field("slv_cmd_err", &self.slv_cmd_err())
            .field("mst_rx_afifo_wfull_err", &self.mst_rx_afifo_wfull_err())
            .field("mst_tx_afifo_rempty_err", &self.mst_tx_afifo_rempty_err())
            .field("app2", &self.app2())
            .field("app1", &self.app1())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - 1: The current data rate of DMA Rx is smaller than that of SPI, which will lose the receive data. 0: Others."]
    #[inline(always)]
    pub fn dma_infifo_full_err(&mut self) -> DMA_INFIFO_FULL_ERR_W<'_, DMA_INT_RAW_SPEC> {
        DMA_INFIFO_FULL_ERR_W::new(self, 0)
    }
    #[doc = "Bit 1 - 1: The current data rate of DMA TX is smaller than that of SPI. SPI will stop in master mode and send out all 0 in slave mode. 0: Others."]
    #[inline(always)]
    pub fn dma_outfifo_empty_err(&mut self) -> DMA_OUTFIFO_EMPTY_ERR_W<'_, DMA_INT_RAW_SPEC> {
        DMA_OUTFIFO_EMPTY_ERR_W::new(self, 1)
    }
    #[doc = "Bit 2 - The raw bit for SPI slave Ex_QPI interrupt. 1: SPI slave mode Ex_QPI transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_ex_qpi(&mut self) -> SLV_EX_QPI_W<'_, DMA_INT_RAW_SPEC> {
        SLV_EX_QPI_W::new(self, 2)
    }
    #[doc = "Bit 3 - The raw bit for SPI slave En_QPI interrupt. 1: SPI slave mode En_QPI transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_en_qpi(&mut self) -> SLV_EN_QPI_W<'_, DMA_INT_RAW_SPEC> {
        SLV_EN_QPI_W::new(self, 3)
    }
    #[doc = "Bit 4 - The raw bit for SPI slave CMD7 interrupt. 1: SPI slave mode CMD7 transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_cmd7(&mut self) -> SLV_CMD7_W<'_, DMA_INT_RAW_SPEC> {
        SLV_CMD7_W::new(self, 4)
    }
    #[doc = "Bit 5 - The raw bit for SPI slave CMD8 interrupt. 1: SPI slave mode CMD8 transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_cmd8(&mut self) -> SLV_CMD8_W<'_, DMA_INT_RAW_SPEC> {
        SLV_CMD8_W::new(self, 5)
    }
    #[doc = "Bit 6 - The raw bit for SPI slave CMD9 interrupt. 1: SPI slave mode CMD9 transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_cmd9(&mut self) -> SLV_CMD9_W<'_, DMA_INT_RAW_SPEC> {
        SLV_CMD9_W::new(self, 6)
    }
    #[doc = "Bit 7 - The raw bit for SPI slave CMDA interrupt. 1: SPI slave mode CMDA transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_cmda(&mut self) -> SLV_CMDA_W<'_, DMA_INT_RAW_SPEC> {
        SLV_CMDA_W::new(self, 7)
    }
    #[doc = "Bit 8 - The raw bit for SPI_SLV_RD_DMA_DONE_INT interrupt. 1: SPI slave mode Rd_DMA transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_rd_dma_done(&mut self) -> SLV_RD_DMA_DONE_W<'_, DMA_INT_RAW_SPEC> {
        SLV_RD_DMA_DONE_W::new(self, 8)
    }
    #[doc = "Bit 9 - The raw bit for SPI_SLV_WR_DMA_DONE_INT interrupt. 1: SPI slave mode Wr_DMA transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_wr_dma_done(&mut self) -> SLV_WR_DMA_DONE_W<'_, DMA_INT_RAW_SPEC> {
        SLV_WR_DMA_DONE_W::new(self, 9)
    }
    #[doc = "Bit 10 - The raw bit for SPI_SLV_RD_BUF_DONE_INT interrupt. 1: SPI slave mode Rd_BUF transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_rd_buf_done(&mut self) -> SLV_RD_BUF_DONE_W<'_, DMA_INT_RAW_SPEC> {
        SLV_RD_BUF_DONE_W::new(self, 10)
    }
    #[doc = "Bit 11 - The raw bit for SPI_SLV_WR_BUF_DONE_INT interrupt. 1: SPI slave mode Wr_BUF transmission is ended. 0: Others."]
    #[inline(always)]
    pub fn slv_wr_buf_done(&mut self) -> SLV_WR_BUF_DONE_W<'_, DMA_INT_RAW_SPEC> {
        SLV_WR_BUF_DONE_W::new(self, 11)
    }
    #[doc = "Bit 12 - The raw bit for SPI_TRANS_DONE_INT interrupt. 1: SPI master mode transmission is ended. 0: others."]
    #[inline(always)]
    pub fn trans_done(&mut self) -> TRANS_DONE_W<'_, DMA_INT_RAW_SPEC> {
        TRANS_DONE_W::new(self, 12)
    }
    #[doc = "Bit 13 - The raw bit for SPI_DMA_SEG_TRANS_DONE_INT interrupt. 1: spi master DMA full-duplex/half-duplex seg-conf-trans ends or slave half-duplex seg-trans ends. And data has been pushed to corresponding memory. 0: seg-conf-trans or seg-trans is not ended or not occurred."]
    #[inline(always)]
    pub fn dma_seg_trans_done(&mut self) -> DMA_SEG_TRANS_DONE_W<'_, DMA_INT_RAW_SPEC> {
        DMA_SEG_TRANS_DONE_W::new(self, 13)
    }
    #[doc = "Bit 14 - The raw bit for SPI_SEG_MAGIC_ERR_INT interrupt. 1: The magic value in CONF buffer is error in the DMA seg-conf-trans. 0: others."]
    #[inline(always)]
    pub fn seg_magic_err(&mut self) -> SEG_MAGIC_ERR_W<'_, DMA_INT_RAW_SPEC> {
        SEG_MAGIC_ERR_W::new(self, 14)
    }
    #[doc = "Bit 15 - The raw bit for SPI_SLV_BUF_ADDR_ERR_INT interrupt. 1: The accessing data address of the current SPI slave mode CPU controlled FD, Wr_BUF or Rd_BUF transmission is bigger than 63. 0: Others."]
    #[inline(always)]
    pub fn slv_buf_addr_err(&mut self) -> SLV_BUF_ADDR_ERR_W<'_, DMA_INT_RAW_SPEC> {
        SLV_BUF_ADDR_ERR_W::new(self, 15)
    }
    #[doc = "Bit 16 - The raw bit for SPI_SLV_CMD_ERR_INT interrupt. 1: The slave command value in the current SPI slave HD mode transmission is not supported. 0: Others."]
    #[inline(always)]
    pub fn slv_cmd_err(&mut self) -> SLV_CMD_ERR_W<'_, DMA_INT_RAW_SPEC> {
        SLV_CMD_ERR_W::new(self, 16)
    }
    #[doc = "Bit 17 - The raw bit for SPI_MST_RX_AFIFO_WFULL_ERR_INT interrupt. 1: There is a RX AFIFO write-full error when SPI inputs data in master mode. 0: Others."]
    #[inline(always)]
    pub fn mst_rx_afifo_wfull_err(&mut self) -> MST_RX_AFIFO_WFULL_ERR_W<'_, DMA_INT_RAW_SPEC> {
        MST_RX_AFIFO_WFULL_ERR_W::new(self, 17)
    }
    #[doc = "Bit 18 - The raw bit for SPI_MST_TX_AFIFO_REMPTY_ERR_INT interrupt. 1: There is a TX BUF AFIFO read-empty error when SPI outputs data in master mode. 0: Others."]
    #[inline(always)]
    pub fn mst_tx_afifo_rempty_err(&mut self) -> MST_TX_AFIFO_REMPTY_ERR_W<'_, DMA_INT_RAW_SPEC> {
        MST_TX_AFIFO_REMPTY_ERR_W::new(self, 18)
    }
    #[doc = "Bit 19 - The raw bit for SPI_APP2_INT interrupt. The value is only controlled by software."]
    #[inline(always)]
    pub fn app2(&mut self) -> APP2_W<'_, DMA_INT_RAW_SPEC> {
        APP2_W::new(self, 19)
    }
    #[doc = "Bit 20 - The raw bit for SPI_APP1_INT interrupt. The value is only controlled by software."]
    #[inline(always)]
    pub fn app1(&mut self) -> APP1_W<'_, DMA_INT_RAW_SPEC> {
        APP1_W::new(self, 20)
    }
}
#[doc = "SPI interrupt raw register\n\nYou can [`read`](crate::Reg::read) this register and get [`dma_int_raw::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_int_raw::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DMA_INT_RAW_SPEC;
impl crate::RegisterSpec for DMA_INT_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_int_raw::R`](R) reader structure"]
impl crate::Readable for DMA_INT_RAW_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dma_int_raw::W`](W) writer structure"]
impl crate::Writable for DMA_INT_RAW_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DMA_INT_RAW to value 0"]
impl crate::Resettable for DMA_INT_RAW_SPEC {}
