#[doc = "Register `SLC0INT_RAW` reader"]
pub type R = crate::R<SLC0INT_RAW_SPEC>;
#[doc = "Register `SLC0INT_RAW` writer"]
pub type W = crate::W<SLC0INT_RAW_SPEC>;
#[doc = "Field `SDIO_SLC_FRHOST_BIT_INT_RAW(0-7)` reader - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
pub type SDIO_SLC_FRHOST_BIT_INT_RAW_R = crate::BitReader;
#[doc = "Field `SDIO_SLC_FRHOST_BIT_INT_RAW(0-7)` writer - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
pub type SDIO_SLC_FRHOST_BIT_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_START_INT_RAW` reader - The raw interrupt status of SLC0_RX_START_INT."]
pub type SDIO_SLC0_RX_START_INT_RAW_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_START_INT_RAW` writer - The raw interrupt status of SLC0_RX_START_INT."]
pub type SDIO_SLC0_RX_START_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TX_START_INT_RAW` reader - The raw interrupt status of SLC0_TX_START_INT."]
pub type SDIO_SLC0_TX_START_INT_RAW_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_START_INT_RAW` writer - The raw interrupt status of SLC0_TX_START_INT."]
pub type SDIO_SLC0_TX_START_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_UDF_INT_RAW` reader - The raw interrupt status of SLC0_RX_UDF_INT."]
pub type SDIO_SLC0_RX_UDF_INT_RAW_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_UDF_INT_RAW` writer - The raw interrupt status of SLC0_RX_UDF_INT."]
pub type SDIO_SLC0_RX_UDF_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TX_OVF_INT_RAW` reader - The raw interrupt status of SLC0_TX_OVF_INT."]
pub type SDIO_SLC0_TX_OVF_INT_RAW_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_OVF_INT_RAW` writer - The raw interrupt status of SLC0_TX_OVF_INT."]
pub type SDIO_SLC0_TX_OVF_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TX_DONE_INT_RAW` reader - The raw interrupt status of SLC0_TX_DONE_INT."]
pub type SDIO_SLC0_TX_DONE_INT_RAW_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_DONE_INT_RAW` writer - The raw interrupt status of SLC0_TX_DONE_INT."]
pub type SDIO_SLC0_TX_DONE_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TX_SUC_EOF_INT_RAW` reader - The raw interrupt status of SLC0_TX_SUC_EOF_INT."]
pub type SDIO_SLC0_TX_SUC_EOF_INT_RAW_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_SUC_EOF_INT_RAW` writer - The raw interrupt status of SLC0_TX_SUC_EOF_INT."]
pub type SDIO_SLC0_TX_SUC_EOF_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_DONE_INT_RAW` reader - The raw interrupt status of SLC0_RX_DONE_INT."]
pub type SDIO_SLC0_RX_DONE_INT_RAW_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_DONE_INT_RAW` writer - The raw interrupt status of SLC0_RX_DONE_INT."]
pub type SDIO_SLC0_RX_DONE_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_EOF_INT_RAW` reader - The raw interrupt status of SLC0_RX_EOF_INT."]
pub type SDIO_SLC0_RX_EOF_INT_RAW_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_EOF_INT_RAW` writer - The raw interrupt status of SLC0_RX_EOF_INT."]
pub type SDIO_SLC0_RX_EOF_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TX_DSCR_ERR_INT_RAW` reader - The raw interrupt status of SLC0_TX_DSCR_ERR_INT."]
pub type SDIO_SLC0_TX_DSCR_ERR_INT_RAW_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_DSCR_ERR_INT_RAW` writer - The raw interrupt status of SLC0_TX_DSCR_ERR_INT."]
pub type SDIO_SLC0_TX_DSCR_ERR_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_DSCR_ERR_INT_RAW` reader - The raw interrupt status of SLC0_RX_DSCR_ERR_INT."]
pub type SDIO_SLC0_RX_DSCR_ERR_INT_RAW_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_DSCR_ERR_INT_RAW` writer - The raw interrupt status of SLC0_RX_DSCR_ERR_INT."]
pub type SDIO_SLC0_RX_DSCR_ERR_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `SDIO_SLC_FRHOST_BIT0_INT_RAW` field.</div>"]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit_int_raw(&self, n: u8) -> SDIO_SLC_FRHOST_BIT_INT_RAW_R {
        #[allow(clippy::no_effect)]
        [(); 8][n as usize];
        SDIO_SLC_FRHOST_BIT_INT_RAW_R::new(((self.bits >> n) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit_int_raw_iter(
        &self,
    ) -> impl Iterator<Item = SDIO_SLC_FRHOST_BIT_INT_RAW_R> + '_ {
        (0..8).map(move |n| SDIO_SLC_FRHOST_BIT_INT_RAW_R::new(((self.bits >> n) & 1) != 0))
    }
    #[doc = "Bit 0 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit0_int_raw(&self) -> SDIO_SLC_FRHOST_BIT_INT_RAW_R {
        SDIO_SLC_FRHOST_BIT_INT_RAW_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit1_int_raw(&self) -> SDIO_SLC_FRHOST_BIT_INT_RAW_R {
        SDIO_SLC_FRHOST_BIT_INT_RAW_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit2_int_raw(&self) -> SDIO_SLC_FRHOST_BIT_INT_RAW_R {
        SDIO_SLC_FRHOST_BIT_INT_RAW_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit3_int_raw(&self) -> SDIO_SLC_FRHOST_BIT_INT_RAW_R {
        SDIO_SLC_FRHOST_BIT_INT_RAW_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit4_int_raw(&self) -> SDIO_SLC_FRHOST_BIT_INT_RAW_R {
        SDIO_SLC_FRHOST_BIT_INT_RAW_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit5_int_raw(&self) -> SDIO_SLC_FRHOST_BIT_INT_RAW_R {
        SDIO_SLC_FRHOST_BIT_INT_RAW_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit6_int_raw(&self) -> SDIO_SLC_FRHOST_BIT_INT_RAW_R {
        SDIO_SLC_FRHOST_BIT_INT_RAW_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit7_int_raw(&self) -> SDIO_SLC_FRHOST_BIT_INT_RAW_R {
        SDIO_SLC_FRHOST_BIT_INT_RAW_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The raw interrupt status of SLC0_RX_START_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_start_int_raw(&self) -> SDIO_SLC0_RX_START_INT_RAW_R {
        SDIO_SLC0_RX_START_INT_RAW_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The raw interrupt status of SLC0_TX_START_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_start_int_raw(&self) -> SDIO_SLC0_TX_START_INT_RAW_R {
        SDIO_SLC0_TX_START_INT_RAW_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - The raw interrupt status of SLC0_RX_UDF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_udf_int_raw(&self) -> SDIO_SLC0_RX_UDF_INT_RAW_R {
        SDIO_SLC0_RX_UDF_INT_RAW_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - The raw interrupt status of SLC0_TX_OVF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_ovf_int_raw(&self) -> SDIO_SLC0_TX_OVF_INT_RAW_R {
        SDIO_SLC0_TX_OVF_INT_RAW_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 14 - The raw interrupt status of SLC0_TX_DONE_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_done_int_raw(&self) -> SDIO_SLC0_TX_DONE_INT_RAW_R {
        SDIO_SLC0_TX_DONE_INT_RAW_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - The raw interrupt status of SLC0_TX_SUC_EOF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_suc_eof_int_raw(&self) -> SDIO_SLC0_TX_SUC_EOF_INT_RAW_R {
        SDIO_SLC0_TX_SUC_EOF_INT_RAW_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - The raw interrupt status of SLC0_RX_DONE_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_done_int_raw(&self) -> SDIO_SLC0_RX_DONE_INT_RAW_R {
        SDIO_SLC0_RX_DONE_INT_RAW_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - The raw interrupt status of SLC0_RX_EOF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_eof_int_raw(&self) -> SDIO_SLC0_RX_EOF_INT_RAW_R {
        SDIO_SLC0_RX_EOF_INT_RAW_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 19 - The raw interrupt status of SLC0_TX_DSCR_ERR_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_dscr_err_int_raw(&self) -> SDIO_SLC0_TX_DSCR_ERR_INT_RAW_R {
        SDIO_SLC0_TX_DSCR_ERR_INT_RAW_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - The raw interrupt status of SLC0_RX_DSCR_ERR_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_dscr_err_int_raw(&self) -> SDIO_SLC0_RX_DSCR_ERR_INT_RAW_R {
        SDIO_SLC0_RX_DSCR_ERR_INT_RAW_R::new(((self.bits >> 20) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC0INT_RAW")
            .field(
                "sdio_slc_frhost_bit0_int_raw",
                &self.sdio_slc_frhost_bit0_int_raw(),
            )
            .field(
                "sdio_slc_frhost_bit1_int_raw",
                &self.sdio_slc_frhost_bit1_int_raw(),
            )
            .field(
                "sdio_slc_frhost_bit2_int_raw",
                &self.sdio_slc_frhost_bit2_int_raw(),
            )
            .field(
                "sdio_slc_frhost_bit3_int_raw",
                &self.sdio_slc_frhost_bit3_int_raw(),
            )
            .field(
                "sdio_slc_frhost_bit4_int_raw",
                &self.sdio_slc_frhost_bit4_int_raw(),
            )
            .field(
                "sdio_slc_frhost_bit5_int_raw",
                &self.sdio_slc_frhost_bit5_int_raw(),
            )
            .field(
                "sdio_slc_frhost_bit6_int_raw",
                &self.sdio_slc_frhost_bit6_int_raw(),
            )
            .field(
                "sdio_slc_frhost_bit7_int_raw",
                &self.sdio_slc_frhost_bit7_int_raw(),
            )
            .field(
                "sdio_slc0_rx_start_int_raw",
                &self.sdio_slc0_rx_start_int_raw(),
            )
            .field(
                "sdio_slc0_tx_start_int_raw",
                &self.sdio_slc0_tx_start_int_raw(),
            )
            .field("sdio_slc0_rx_udf_int_raw", &self.sdio_slc0_rx_udf_int_raw())
            .field("sdio_slc0_tx_ovf_int_raw", &self.sdio_slc0_tx_ovf_int_raw())
            .field(
                "sdio_slc0_tx_done_int_raw",
                &self.sdio_slc0_tx_done_int_raw(),
            )
            .field(
                "sdio_slc0_tx_suc_eof_int_raw",
                &self.sdio_slc0_tx_suc_eof_int_raw(),
            )
            .field(
                "sdio_slc0_rx_done_int_raw",
                &self.sdio_slc0_rx_done_int_raw(),
            )
            .field("sdio_slc0_rx_eof_int_raw", &self.sdio_slc0_rx_eof_int_raw())
            .field(
                "sdio_slc0_tx_dscr_err_int_raw",
                &self.sdio_slc0_tx_dscr_err_int_raw(),
            )
            .field(
                "sdio_slc0_rx_dscr_err_int_raw",
                &self.sdio_slc0_rx_dscr_err_int_raw(),
            )
            .finish()
    }
}
impl W {
    #[doc = "The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `SDIO_SLC_FRHOST_BIT0_INT_RAW` field.</div>"]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit_int_raw(
        &mut self,
        n: u8,
    ) -> SDIO_SLC_FRHOST_BIT_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 8][n as usize];
        SDIO_SLC_FRHOST_BIT_INT_RAW_W::new(self, n)
    }
    #[doc = "Bit 0 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit0_int_raw(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_RAW_W::new(self, 0)
    }
    #[doc = "Bit 1 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit1_int_raw(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_RAW_W::new(self, 1)
    }
    #[doc = "Bit 2 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit2_int_raw(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_RAW_W::new(self, 2)
    }
    #[doc = "Bit 3 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit3_int_raw(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_RAW_W::new(self, 3)
    }
    #[doc = "Bit 4 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit4_int_raw(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_RAW_W::new(self, 4)
    }
    #[doc = "Bit 5 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit5_int_raw(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_RAW_W::new(self, 5)
    }
    #[doc = "Bit 6 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit6_int_raw(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_RAW_W::new(self, 6)
    }
    #[doc = "Bit 7 - The raw interrupt status of SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit7_int_raw(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_RAW_W::new(self, 7)
    }
    #[doc = "Bit 8 - The raw interrupt status of SLC0_RX_START_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_start_int_raw(
        &mut self,
    ) -> SDIO_SLC0_RX_START_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC0_RX_START_INT_RAW_W::new(self, 8)
    }
    #[doc = "Bit 9 - The raw interrupt status of SLC0_TX_START_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_start_int_raw(
        &mut self,
    ) -> SDIO_SLC0_TX_START_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC0_TX_START_INT_RAW_W::new(self, 9)
    }
    #[doc = "Bit 10 - The raw interrupt status of SLC0_RX_UDF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_udf_int_raw(&mut self) -> SDIO_SLC0_RX_UDF_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC0_RX_UDF_INT_RAW_W::new(self, 10)
    }
    #[doc = "Bit 11 - The raw interrupt status of SLC0_TX_OVF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_ovf_int_raw(&mut self) -> SDIO_SLC0_TX_OVF_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC0_TX_OVF_INT_RAW_W::new(self, 11)
    }
    #[doc = "Bit 14 - The raw interrupt status of SLC0_TX_DONE_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_done_int_raw(
        &mut self,
    ) -> SDIO_SLC0_TX_DONE_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC0_TX_DONE_INT_RAW_W::new(self, 14)
    }
    #[doc = "Bit 15 - The raw interrupt status of SLC0_TX_SUC_EOF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_suc_eof_int_raw(
        &mut self,
    ) -> SDIO_SLC0_TX_SUC_EOF_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC0_TX_SUC_EOF_INT_RAW_W::new(self, 15)
    }
    #[doc = "Bit 16 - The raw interrupt status of SLC0_RX_DONE_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_done_int_raw(
        &mut self,
    ) -> SDIO_SLC0_RX_DONE_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC0_RX_DONE_INT_RAW_W::new(self, 16)
    }
    #[doc = "Bit 17 - The raw interrupt status of SLC0_RX_EOF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_eof_int_raw(&mut self) -> SDIO_SLC0_RX_EOF_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC0_RX_EOF_INT_RAW_W::new(self, 17)
    }
    #[doc = "Bit 19 - The raw interrupt status of SLC0_TX_DSCR_ERR_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_dscr_err_int_raw(
        &mut self,
    ) -> SDIO_SLC0_TX_DSCR_ERR_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC0_TX_DSCR_ERR_INT_RAW_W::new(self, 19)
    }
    #[doc = "Bit 20 - The raw interrupt status of SLC0_RX_DSCR_ERR_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_dscr_err_int_raw(
        &mut self,
    ) -> SDIO_SLC0_RX_DSCR_ERR_INT_RAW_W<'_, SLC0INT_RAW_SPEC> {
        SDIO_SLC0_RX_DSCR_ERR_INT_RAW_W::new(self, 20)
    }
}
#[doc = "SLC0 to slave raw interrupt status\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0int_raw::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0int_raw::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC0INT_RAW_SPEC;
impl crate::RegisterSpec for SLC0INT_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc0int_raw::R`](R) reader structure"]
impl crate::Readable for SLC0INT_RAW_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slc0int_raw::W`](W) writer structure"]
impl crate::Writable for SLC0INT_RAW_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC0INT_RAW to value 0"]
impl crate::Resettable for SLC0INT_RAW_SPEC {}
