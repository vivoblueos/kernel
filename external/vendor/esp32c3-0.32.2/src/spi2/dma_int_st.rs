#[doc = "Register `DMA_INT_ST` reader"]
pub type R = crate::R<DMA_INT_ST_SPEC>;
#[doc = "Field `DMA_INFIFO_FULL_ERR` reader - The status bit for SPI_DMA_INFIFO_FULL_ERR_INT interrupt."]
pub type DMA_INFIFO_FULL_ERR_R = crate::BitReader;
#[doc = "Field `DMA_OUTFIFO_EMPTY_ERR` reader - The status bit for SPI_DMA_OUTFIFO_EMPTY_ERR_INT interrupt."]
pub type DMA_OUTFIFO_EMPTY_ERR_R = crate::BitReader;
#[doc = "Field `SLV_EX_QPI` reader - The status bit for SPI slave Ex_QPI interrupt."]
pub type SLV_EX_QPI_R = crate::BitReader;
#[doc = "Field `SLV_EN_QPI` reader - The status bit for SPI slave En_QPI interrupt."]
pub type SLV_EN_QPI_R = crate::BitReader;
#[doc = "Field `SLV_CMD7` reader - The status bit for SPI slave CMD7 interrupt."]
pub type SLV_CMD7_R = crate::BitReader;
#[doc = "Field `SLV_CMD8` reader - The status bit for SPI slave CMD8 interrupt."]
pub type SLV_CMD8_R = crate::BitReader;
#[doc = "Field `SLV_CMD9` reader - The status bit for SPI slave CMD9 interrupt."]
pub type SLV_CMD9_R = crate::BitReader;
#[doc = "Field `SLV_CMDA` reader - The status bit for SPI slave CMDA interrupt."]
pub type SLV_CMDA_R = crate::BitReader;
#[doc = "Field `SLV_RD_DMA_DONE` reader - The status bit for SPI_SLV_RD_DMA_DONE_INT interrupt."]
pub type SLV_RD_DMA_DONE_R = crate::BitReader;
#[doc = "Field `SLV_WR_DMA_DONE` reader - The status bit for SPI_SLV_WR_DMA_DONE_INT interrupt."]
pub type SLV_WR_DMA_DONE_R = crate::BitReader;
#[doc = "Field `SLV_RD_BUF_DONE` reader - The status bit for SPI_SLV_RD_BUF_DONE_INT interrupt."]
pub type SLV_RD_BUF_DONE_R = crate::BitReader;
#[doc = "Field `SLV_WR_BUF_DONE` reader - The status bit for SPI_SLV_WR_BUF_DONE_INT interrupt."]
pub type SLV_WR_BUF_DONE_R = crate::BitReader;
#[doc = "Field `TRANS_DONE` reader - The status bit for SPI_TRANS_DONE_INT interrupt."]
pub type TRANS_DONE_R = crate::BitReader;
#[doc = "Field `DMA_SEG_TRANS_DONE` reader - The status bit for SPI_DMA_SEG_TRANS_DONE_INT interrupt."]
pub type DMA_SEG_TRANS_DONE_R = crate::BitReader;
#[doc = "Field `SEG_MAGIC_ERR` reader - The status bit for SPI_SEG_MAGIC_ERR_INT interrupt."]
pub type SEG_MAGIC_ERR_R = crate::BitReader;
#[doc = "Field `SLV_BUF_ADDR_ERR` reader - The status bit for SPI_SLV_BUF_ADDR_ERR_INT interrupt."]
pub type SLV_BUF_ADDR_ERR_R = crate::BitReader;
#[doc = "Field `SLV_CMD_ERR` reader - The status bit for SPI_SLV_CMD_ERR_INT interrupt."]
pub type SLV_CMD_ERR_R = crate::BitReader;
#[doc = "Field `MST_RX_AFIFO_WFULL_ERR` reader - The status bit for SPI_MST_RX_AFIFO_WFULL_ERR_INT interrupt."]
pub type MST_RX_AFIFO_WFULL_ERR_R = crate::BitReader;
#[doc = "Field `MST_TX_AFIFO_REMPTY_ERR` reader - The status bit for SPI_MST_TX_AFIFO_REMPTY_ERR_INT interrupt."]
pub type MST_TX_AFIFO_REMPTY_ERR_R = crate::BitReader;
#[doc = "Field `APP2` reader - The status bit for SPI_APP2_INT interrupt."]
pub type APP2_R = crate::BitReader;
#[doc = "Field `APP1` reader - The status bit for SPI_APP1_INT interrupt."]
pub type APP1_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The status bit for SPI_DMA_INFIFO_FULL_ERR_INT interrupt."]
    #[inline(always)]
    pub fn dma_infifo_full_err(&self) -> DMA_INFIFO_FULL_ERR_R {
        DMA_INFIFO_FULL_ERR_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The status bit for SPI_DMA_OUTFIFO_EMPTY_ERR_INT interrupt."]
    #[inline(always)]
    pub fn dma_outfifo_empty_err(&self) -> DMA_OUTFIFO_EMPTY_ERR_R {
        DMA_OUTFIFO_EMPTY_ERR_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The status bit for SPI slave Ex_QPI interrupt."]
    #[inline(always)]
    pub fn slv_ex_qpi(&self) -> SLV_EX_QPI_R {
        SLV_EX_QPI_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The status bit for SPI slave En_QPI interrupt."]
    #[inline(always)]
    pub fn slv_en_qpi(&self) -> SLV_EN_QPI_R {
        SLV_EN_QPI_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The status bit for SPI slave CMD7 interrupt."]
    #[inline(always)]
    pub fn slv_cmd7(&self) -> SLV_CMD7_R {
        SLV_CMD7_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The status bit for SPI slave CMD8 interrupt."]
    #[inline(always)]
    pub fn slv_cmd8(&self) -> SLV_CMD8_R {
        SLV_CMD8_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The status bit for SPI slave CMD9 interrupt."]
    #[inline(always)]
    pub fn slv_cmd9(&self) -> SLV_CMD9_R {
        SLV_CMD9_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The status bit for SPI slave CMDA interrupt."]
    #[inline(always)]
    pub fn slv_cmda(&self) -> SLV_CMDA_R {
        SLV_CMDA_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The status bit for SPI_SLV_RD_DMA_DONE_INT interrupt."]
    #[inline(always)]
    pub fn slv_rd_dma_done(&self) -> SLV_RD_DMA_DONE_R {
        SLV_RD_DMA_DONE_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The status bit for SPI_SLV_WR_DMA_DONE_INT interrupt."]
    #[inline(always)]
    pub fn slv_wr_dma_done(&self) -> SLV_WR_DMA_DONE_R {
        SLV_WR_DMA_DONE_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - The status bit for SPI_SLV_RD_BUF_DONE_INT interrupt."]
    #[inline(always)]
    pub fn slv_rd_buf_done(&self) -> SLV_RD_BUF_DONE_R {
        SLV_RD_BUF_DONE_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - The status bit for SPI_SLV_WR_BUF_DONE_INT interrupt."]
    #[inline(always)]
    pub fn slv_wr_buf_done(&self) -> SLV_WR_BUF_DONE_R {
        SLV_WR_BUF_DONE_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - The status bit for SPI_TRANS_DONE_INT interrupt."]
    #[inline(always)]
    pub fn trans_done(&self) -> TRANS_DONE_R {
        TRANS_DONE_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - The status bit for SPI_DMA_SEG_TRANS_DONE_INT interrupt."]
    #[inline(always)]
    pub fn dma_seg_trans_done(&self) -> DMA_SEG_TRANS_DONE_R {
        DMA_SEG_TRANS_DONE_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - The status bit for SPI_SEG_MAGIC_ERR_INT interrupt."]
    #[inline(always)]
    pub fn seg_magic_err(&self) -> SEG_MAGIC_ERR_R {
        SEG_MAGIC_ERR_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - The status bit for SPI_SLV_BUF_ADDR_ERR_INT interrupt."]
    #[inline(always)]
    pub fn slv_buf_addr_err(&self) -> SLV_BUF_ADDR_ERR_R {
        SLV_BUF_ADDR_ERR_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - The status bit for SPI_SLV_CMD_ERR_INT interrupt."]
    #[inline(always)]
    pub fn slv_cmd_err(&self) -> SLV_CMD_ERR_R {
        SLV_CMD_ERR_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - The status bit for SPI_MST_RX_AFIFO_WFULL_ERR_INT interrupt."]
    #[inline(always)]
    pub fn mst_rx_afifo_wfull_err(&self) -> MST_RX_AFIFO_WFULL_ERR_R {
        MST_RX_AFIFO_WFULL_ERR_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - The status bit for SPI_MST_TX_AFIFO_REMPTY_ERR_INT interrupt."]
    #[inline(always)]
    pub fn mst_tx_afifo_rempty_err(&self) -> MST_TX_AFIFO_REMPTY_ERR_R {
        MST_TX_AFIFO_REMPTY_ERR_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - The status bit for SPI_APP2_INT interrupt."]
    #[inline(always)]
    pub fn app2(&self) -> APP2_R {
        APP2_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - The status bit for SPI_APP1_INT interrupt."]
    #[inline(always)]
    pub fn app1(&self) -> APP1_R {
        APP1_R::new(((self.bits >> 20) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DMA_INT_ST")
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
#[doc = "SPI DMA interrupt status register\n\nYou can [`read`](crate::Reg::read) this register and get [`dma_int_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DMA_INT_ST_SPEC;
impl crate::RegisterSpec for DMA_INT_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_int_st::R`](R) reader structure"]
impl crate::Readable for DMA_INT_ST_SPEC {}
#[doc = "`reset()` method sets DMA_INT_ST to value 0"]
impl crate::Resettable for DMA_INT_ST_SPEC {}
