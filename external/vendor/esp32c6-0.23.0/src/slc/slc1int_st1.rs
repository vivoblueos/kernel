#[doc = "Register `SLC1INT_ST1` reader"]
pub type R = crate::R<SLC1INT_ST1_SPEC>;
#[doc = "Field `SDIO_SLC_FRHOST_BIT_INT_ST1(0-7)` reader - The masked interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
pub type SDIO_SLC_FRHOST_BIT_INT_ST1_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RX_START_INT_ST1` reader - The masked interrupt status of SLC1_RX_START_INT."]
pub type SDIO_SLC1_RX_START_INT_ST1_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_TX_START_INT_ST1` reader - The masked interrupt status of SLC1_TX_START_INT."]
pub type SDIO_SLC1_TX_START_INT_ST1_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RX_UDF_INT_ST1` reader - The masked interrupt status of SLC1_RX_UDF_INT."]
pub type SDIO_SLC1_RX_UDF_INT_ST1_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_TX_OVF_INT_ST1` reader - The masked interrupt status of SLC1_TX_OVF_INT."]
pub type SDIO_SLC1_TX_OVF_INT_ST1_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_TX_DONE_INT_ST1` reader - The masked interrupt status of SLC1_TX_DONE_INT."]
pub type SDIO_SLC1_TX_DONE_INT_ST1_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_TX_SUC_EOF_INT_ST1` reader - The masked interrupt status of SLC1_TX_SUC_EOF_INT."]
pub type SDIO_SLC1_TX_SUC_EOF_INT_ST1_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RX_DONE_INT_ST1` reader - The masked interrupt status of SLC1_RX_DONE_INT."]
pub type SDIO_SLC1_RX_DONE_INT_ST1_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RX_EOF_INT_ST1` reader - The masked interrupt status of SLC1_RX_EOF_INT."]
pub type SDIO_SLC1_RX_EOF_INT_ST1_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_TX_DSCR_ERR_INT_ST1` reader - The masked interrupt status of SLC1_TX_DSCR_ERR_INT."]
pub type SDIO_SLC1_TX_DSCR_ERR_INT_ST1_R = crate::BitReader;
#[doc = "Field `SDIO_SLC1_RX_DSCR_ERR_INT_ST1` reader - The masked interrupt status of SLC1_RX_DSCR_ERR_INT."]
pub type SDIO_SLC1_RX_DSCR_ERR_INT_ST1_R = crate::BitReader;
impl R {
    #[doc = "The masked interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `SDIO_SLC_FRHOST_BIT0_INT_ST1` field.</div>"]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit_int_st1(&self, n: u8) -> SDIO_SLC_FRHOST_BIT_INT_ST1_R {
        #[allow(clippy::no_effect)]
        [(); 8][n as usize];
        SDIO_SLC_FRHOST_BIT_INT_ST1_R::new(((self.bits >> n) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "The masked interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit_int_st1_iter(
        &self,
    ) -> impl Iterator<Item = SDIO_SLC_FRHOST_BIT_INT_ST1_R> + '_ {
        (0..8).map(move |n| SDIO_SLC_FRHOST_BIT_INT_ST1_R::new(((self.bits >> n) & 1) != 0))
    }
    #[doc = "Bit 0 - The masked interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit0_int_st1(&self) -> SDIO_SLC_FRHOST_BIT_INT_ST1_R {
        SDIO_SLC_FRHOST_BIT_INT_ST1_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The masked interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit1_int_st1(&self) -> SDIO_SLC_FRHOST_BIT_INT_ST1_R {
        SDIO_SLC_FRHOST_BIT_INT_ST1_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The masked interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit2_int_st1(&self) -> SDIO_SLC_FRHOST_BIT_INT_ST1_R {
        SDIO_SLC_FRHOST_BIT_INT_ST1_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The masked interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit3_int_st1(&self) -> SDIO_SLC_FRHOST_BIT_INT_ST1_R {
        SDIO_SLC_FRHOST_BIT_INT_ST1_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The masked interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit4_int_st1(&self) -> SDIO_SLC_FRHOST_BIT_INT_ST1_R {
        SDIO_SLC_FRHOST_BIT_INT_ST1_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The masked interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit5_int_st1(&self) -> SDIO_SLC_FRHOST_BIT_INT_ST1_R {
        SDIO_SLC_FRHOST_BIT_INT_ST1_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The masked interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit6_int_st1(&self) -> SDIO_SLC_FRHOST_BIT_INT_ST1_R {
        SDIO_SLC_FRHOST_BIT_INT_ST1_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The masked interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit7_int_st1(&self) -> SDIO_SLC_FRHOST_BIT_INT_ST1_R {
        SDIO_SLC_FRHOST_BIT_INT_ST1_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The masked interrupt status of SLC1_RX_START_INT."]
    #[inline(always)]
    pub fn sdio_slc1_rx_start_int_st1(&self) -> SDIO_SLC1_RX_START_INT_ST1_R {
        SDIO_SLC1_RX_START_INT_ST1_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The masked interrupt status of SLC1_TX_START_INT."]
    #[inline(always)]
    pub fn sdio_slc1_tx_start_int_st1(&self) -> SDIO_SLC1_TX_START_INT_ST1_R {
        SDIO_SLC1_TX_START_INT_ST1_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - The masked interrupt status of SLC1_RX_UDF_INT."]
    #[inline(always)]
    pub fn sdio_slc1_rx_udf_int_st1(&self) -> SDIO_SLC1_RX_UDF_INT_ST1_R {
        SDIO_SLC1_RX_UDF_INT_ST1_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - The masked interrupt status of SLC1_TX_OVF_INT."]
    #[inline(always)]
    pub fn sdio_slc1_tx_ovf_int_st1(&self) -> SDIO_SLC1_TX_OVF_INT_ST1_R {
        SDIO_SLC1_TX_OVF_INT_ST1_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 14 - The masked interrupt status of SLC1_TX_DONE_INT."]
    #[inline(always)]
    pub fn sdio_slc1_tx_done_int_st1(&self) -> SDIO_SLC1_TX_DONE_INT_ST1_R {
        SDIO_SLC1_TX_DONE_INT_ST1_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - The masked interrupt status of SLC1_TX_SUC_EOF_INT."]
    #[inline(always)]
    pub fn sdio_slc1_tx_suc_eof_int_st1(&self) -> SDIO_SLC1_TX_SUC_EOF_INT_ST1_R {
        SDIO_SLC1_TX_SUC_EOF_INT_ST1_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - The masked interrupt status of SLC1_RX_DONE_INT."]
    #[inline(always)]
    pub fn sdio_slc1_rx_done_int_st1(&self) -> SDIO_SLC1_RX_DONE_INT_ST1_R {
        SDIO_SLC1_RX_DONE_INT_ST1_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - The masked interrupt status of SLC1_RX_EOF_INT."]
    #[inline(always)]
    pub fn sdio_slc1_rx_eof_int_st1(&self) -> SDIO_SLC1_RX_EOF_INT_ST1_R {
        SDIO_SLC1_RX_EOF_INT_ST1_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 19 - The masked interrupt status of SLC1_TX_DSCR_ERR_INT."]
    #[inline(always)]
    pub fn sdio_slc1_tx_dscr_err_int_st1(&self) -> SDIO_SLC1_TX_DSCR_ERR_INT_ST1_R {
        SDIO_SLC1_TX_DSCR_ERR_INT_ST1_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - The masked interrupt status of SLC1_RX_DSCR_ERR_INT."]
    #[inline(always)]
    pub fn sdio_slc1_rx_dscr_err_int_st1(&self) -> SDIO_SLC1_RX_DSCR_ERR_INT_ST1_R {
        SDIO_SLC1_RX_DSCR_ERR_INT_ST1_R::new(((self.bits >> 20) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC1INT_ST1")
            .field(
                "sdio_slc_frhost_bit0_int_st1",
                &self.sdio_slc_frhost_bit0_int_st1(),
            )
            .field(
                "sdio_slc_frhost_bit1_int_st1",
                &self.sdio_slc_frhost_bit1_int_st1(),
            )
            .field(
                "sdio_slc_frhost_bit2_int_st1",
                &self.sdio_slc_frhost_bit2_int_st1(),
            )
            .field(
                "sdio_slc_frhost_bit3_int_st1",
                &self.sdio_slc_frhost_bit3_int_st1(),
            )
            .field(
                "sdio_slc_frhost_bit4_int_st1",
                &self.sdio_slc_frhost_bit4_int_st1(),
            )
            .field(
                "sdio_slc_frhost_bit5_int_st1",
                &self.sdio_slc_frhost_bit5_int_st1(),
            )
            .field(
                "sdio_slc_frhost_bit6_int_st1",
                &self.sdio_slc_frhost_bit6_int_st1(),
            )
            .field(
                "sdio_slc_frhost_bit7_int_st1",
                &self.sdio_slc_frhost_bit7_int_st1(),
            )
            .field(
                "sdio_slc1_rx_start_int_st1",
                &self.sdio_slc1_rx_start_int_st1(),
            )
            .field(
                "sdio_slc1_tx_start_int_st1",
                &self.sdio_slc1_tx_start_int_st1(),
            )
            .field("sdio_slc1_rx_udf_int_st1", &self.sdio_slc1_rx_udf_int_st1())
            .field("sdio_slc1_tx_ovf_int_st1", &self.sdio_slc1_tx_ovf_int_st1())
            .field(
                "sdio_slc1_tx_done_int_st1",
                &self.sdio_slc1_tx_done_int_st1(),
            )
            .field(
                "sdio_slc1_tx_suc_eof_int_st1",
                &self.sdio_slc1_tx_suc_eof_int_st1(),
            )
            .field(
                "sdio_slc1_rx_done_int_st1",
                &self.sdio_slc1_rx_done_int_st1(),
            )
            .field("sdio_slc1_rx_eof_int_st1", &self.sdio_slc1_rx_eof_int_st1())
            .field(
                "sdio_slc1_tx_dscr_err_int_st1",
                &self.sdio_slc1_tx_dscr_err_int_st1(),
            )
            .field(
                "sdio_slc1_rx_dscr_err_int_st1",
                &self.sdio_slc1_rx_dscr_err_int_st1(),
            )
            .finish()
    }
}
#[doc = "SLC1 to slave masked interrupt status\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1int_st1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC1INT_ST1_SPEC;
impl crate::RegisterSpec for SLC1INT_ST1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc1int_st1::R`](R) reader structure"]
impl crate::Readable for SLC1INT_ST1_SPEC {}
#[doc = "`reset()` method sets SLC1INT_ST1 to value 0"]
impl crate::Resettable for SLC1INT_ST1_SPEC {}
