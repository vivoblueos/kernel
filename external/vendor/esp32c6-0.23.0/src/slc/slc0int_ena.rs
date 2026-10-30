#[doc = "Register `SLC0INT_ENA` reader"]
pub type R = crate::R<SLC0INT_ENA_SPEC>;
#[doc = "Register `SLC0INT_ENA` writer"]
pub type W = crate::W<SLC0INT_ENA_SPEC>;
#[doc = "Field `SDIO_SLC_FRHOST_BIT_INT_ENA(0-7)` reader - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
pub type SDIO_SLC_FRHOST_BIT_INT_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLC_FRHOST_BIT_INT_ENA(0-7)` writer - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
pub type SDIO_SLC_FRHOST_BIT_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_ENAART_INT_ENA` reader - Write 1 to enable interrupt SLC0_RX_ENAART_INT."]
pub type SDIO_SLC0_RX_ENAART_INT_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_ENAART_INT_ENA` writer - Write 1 to enable interrupt SLC0_RX_ENAART_INT."]
pub type SDIO_SLC0_RX_ENAART_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TX_ENAART_INT_ENA` reader - Write 1 to enable interrupt SLC0_TX_ENAART_INT."]
pub type SDIO_SLC0_TX_ENAART_INT_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_ENAART_INT_ENA` writer - Write 1 to enable interrupt SLC0_TX_ENAART_INT."]
pub type SDIO_SLC0_TX_ENAART_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_UDF_INT_ENA` reader - Write 1 to enable interrupt SLC0_RX_UDF_INT."]
pub type SDIO_SLC0_RX_UDF_INT_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_UDF_INT_ENA` writer - Write 1 to enable interrupt SLC0_RX_UDF_INT."]
pub type SDIO_SLC0_RX_UDF_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TX_OVF_INT_ENA` reader - Write 1 to enable interrupt SLC0_TX_OVF_INT."]
pub type SDIO_SLC0_TX_OVF_INT_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_OVF_INT_ENA` writer - Write 1 to enable interrupt SLC0_TX_OVF_INT."]
pub type SDIO_SLC0_TX_OVF_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TX_DONE_INT_ENA` reader - Write 1 to enable interrupt SLC0_TX_DONE_INT."]
pub type SDIO_SLC0_TX_DONE_INT_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_DONE_INT_ENA` writer - Write 1 to enable interrupt SLC0_TX_DONE_INT."]
pub type SDIO_SLC0_TX_DONE_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TX_SUC_EOF_INT_ENA` reader - Write 1 to enable interrupt SLC0_TX_SUC_EOF_INT."]
pub type SDIO_SLC0_TX_SUC_EOF_INT_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_SUC_EOF_INT_ENA` writer - Write 1 to enable interrupt SLC0_TX_SUC_EOF_INT."]
pub type SDIO_SLC0_TX_SUC_EOF_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_DONE_INT_ENA` reader - Write 1 to enable interrupt SLC0_RX_DONE_INT."]
pub type SDIO_SLC0_RX_DONE_INT_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_DONE_INT_ENA` writer - Write 1 to enable interrupt SLC0_RX_DONE_INT."]
pub type SDIO_SLC0_RX_DONE_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_EOF_INT_ENA` reader - Write 1 to enable interrupt SLC0_RX_EOF_INT."]
pub type SDIO_SLC0_RX_EOF_INT_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_EOF_INT_ENA` writer - Write 1 to enable interrupt SLC0_RX_EOF_INT."]
pub type SDIO_SLC0_RX_EOF_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_TX_DSCR_ERR_INT_ENA` reader - Write 1 to enable interrupt SLC0_TX_DSCR_ERR_INT."]
pub type SDIO_SLC0_TX_DSCR_ERR_INT_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_TX_DSCR_ERR_INT_ENA` writer - Write 1 to enable interrupt SLC0_TX_DSCR_ERR_INT."]
pub type SDIO_SLC0_TX_DSCR_ERR_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_RX_DSCR_ERR_INT_ENA` reader - Write 1 to enable interrupt SLC0_RX_DSCR_ERR_INT."]
pub type SDIO_SLC0_RX_DSCR_ERR_INT_ENA_R = crate::BitReader;
#[doc = "Field `SDIO_SLC0_RX_DSCR_ERR_INT_ENA` writer - Write 1 to enable interrupt SLC0_RX_DSCR_ERR_INT."]
pub type SDIO_SLC0_RX_DSCR_ERR_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `SDIO_SLC_FRHOST_BIT0_INT_ENA` field.</div>"]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit_int_ena(&self, n: u8) -> SDIO_SLC_FRHOST_BIT_INT_ENA_R {
        #[allow(clippy::no_effect)]
        [(); 8][n as usize];
        SDIO_SLC_FRHOST_BIT_INT_ENA_R::new(((self.bits >> n) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit_int_ena_iter(
        &self,
    ) -> impl Iterator<Item = SDIO_SLC_FRHOST_BIT_INT_ENA_R> + '_ {
        (0..8).map(move |n| SDIO_SLC_FRHOST_BIT_INT_ENA_R::new(((self.bits >> n) & 1) != 0))
    }
    #[doc = "Bit 0 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit0_int_ena(&self) -> SDIO_SLC_FRHOST_BIT_INT_ENA_R {
        SDIO_SLC_FRHOST_BIT_INT_ENA_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit1_int_ena(&self) -> SDIO_SLC_FRHOST_BIT_INT_ENA_R {
        SDIO_SLC_FRHOST_BIT_INT_ENA_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit2_int_ena(&self) -> SDIO_SLC_FRHOST_BIT_INT_ENA_R {
        SDIO_SLC_FRHOST_BIT_INT_ENA_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit3_int_ena(&self) -> SDIO_SLC_FRHOST_BIT_INT_ENA_R {
        SDIO_SLC_FRHOST_BIT_INT_ENA_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit4_int_ena(&self) -> SDIO_SLC_FRHOST_BIT_INT_ENA_R {
        SDIO_SLC_FRHOST_BIT_INT_ENA_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit5_int_ena(&self) -> SDIO_SLC_FRHOST_BIT_INT_ENA_R {
        SDIO_SLC_FRHOST_BIT_INT_ENA_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit6_int_ena(&self) -> SDIO_SLC_FRHOST_BIT_INT_ENA_R {
        SDIO_SLC_FRHOST_BIT_INT_ENA_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit7_int_ena(&self) -> SDIO_SLC_FRHOST_BIT_INT_ENA_R {
        SDIO_SLC_FRHOST_BIT_INT_ENA_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Write 1 to enable interrupt SLC0_RX_ENAART_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_enaart_int_ena(&self) -> SDIO_SLC0_RX_ENAART_INT_ENA_R {
        SDIO_SLC0_RX_ENAART_INT_ENA_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Write 1 to enable interrupt SLC0_TX_ENAART_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_enaart_int_ena(&self) -> SDIO_SLC0_TX_ENAART_INT_ENA_R {
        SDIO_SLC0_TX_ENAART_INT_ENA_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Write 1 to enable interrupt SLC0_RX_UDF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_udf_int_ena(&self) -> SDIO_SLC0_RX_UDF_INT_ENA_R {
        SDIO_SLC0_RX_UDF_INT_ENA_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Write 1 to enable interrupt SLC0_TX_OVF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_ovf_int_ena(&self) -> SDIO_SLC0_TX_OVF_INT_ENA_R {
        SDIO_SLC0_TX_OVF_INT_ENA_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 14 - Write 1 to enable interrupt SLC0_TX_DONE_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_done_int_ena(&self) -> SDIO_SLC0_TX_DONE_INT_ENA_R {
        SDIO_SLC0_TX_DONE_INT_ENA_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Write 1 to enable interrupt SLC0_TX_SUC_EOF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_suc_eof_int_ena(&self) -> SDIO_SLC0_TX_SUC_EOF_INT_ENA_R {
        SDIO_SLC0_TX_SUC_EOF_INT_ENA_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Write 1 to enable interrupt SLC0_RX_DONE_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_done_int_ena(&self) -> SDIO_SLC0_RX_DONE_INT_ENA_R {
        SDIO_SLC0_RX_DONE_INT_ENA_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Write 1 to enable interrupt SLC0_RX_EOF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_eof_int_ena(&self) -> SDIO_SLC0_RX_EOF_INT_ENA_R {
        SDIO_SLC0_RX_EOF_INT_ENA_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 19 - Write 1 to enable interrupt SLC0_TX_DSCR_ERR_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_dscr_err_int_ena(&self) -> SDIO_SLC0_TX_DSCR_ERR_INT_ENA_R {
        SDIO_SLC0_TX_DSCR_ERR_INT_ENA_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Write 1 to enable interrupt SLC0_RX_DSCR_ERR_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_dscr_err_int_ena(&self) -> SDIO_SLC0_RX_DSCR_ERR_INT_ENA_R {
        SDIO_SLC0_RX_DSCR_ERR_INT_ENA_R::new(((self.bits >> 20) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC0INT_ENA")
            .field(
                "sdio_slc_frhost_bit0_int_ena",
                &self.sdio_slc_frhost_bit0_int_ena(),
            )
            .field(
                "sdio_slc_frhost_bit1_int_ena",
                &self.sdio_slc_frhost_bit1_int_ena(),
            )
            .field(
                "sdio_slc_frhost_bit2_int_ena",
                &self.sdio_slc_frhost_bit2_int_ena(),
            )
            .field(
                "sdio_slc_frhost_bit3_int_ena",
                &self.sdio_slc_frhost_bit3_int_ena(),
            )
            .field(
                "sdio_slc_frhost_bit4_int_ena",
                &self.sdio_slc_frhost_bit4_int_ena(),
            )
            .field(
                "sdio_slc_frhost_bit5_int_ena",
                &self.sdio_slc_frhost_bit5_int_ena(),
            )
            .field(
                "sdio_slc_frhost_bit6_int_ena",
                &self.sdio_slc_frhost_bit6_int_ena(),
            )
            .field(
                "sdio_slc_frhost_bit7_int_ena",
                &self.sdio_slc_frhost_bit7_int_ena(),
            )
            .field(
                "sdio_slc0_rx_enaart_int_ena",
                &self.sdio_slc0_rx_enaart_int_ena(),
            )
            .field(
                "sdio_slc0_tx_enaart_int_ena",
                &self.sdio_slc0_tx_enaart_int_ena(),
            )
            .field("sdio_slc0_rx_udf_int_ena", &self.sdio_slc0_rx_udf_int_ena())
            .field("sdio_slc0_tx_ovf_int_ena", &self.sdio_slc0_tx_ovf_int_ena())
            .field(
                "sdio_slc0_tx_done_int_ena",
                &self.sdio_slc0_tx_done_int_ena(),
            )
            .field(
                "sdio_slc0_tx_suc_eof_int_ena",
                &self.sdio_slc0_tx_suc_eof_int_ena(),
            )
            .field(
                "sdio_slc0_rx_done_int_ena",
                &self.sdio_slc0_rx_done_int_ena(),
            )
            .field("sdio_slc0_rx_eof_int_ena", &self.sdio_slc0_rx_eof_int_ena())
            .field(
                "sdio_slc0_tx_dscr_err_int_ena",
                &self.sdio_slc0_tx_dscr_err_int_ena(),
            )
            .field(
                "sdio_slc0_rx_dscr_err_int_ena",
                &self.sdio_slc0_rx_dscr_err_int_ena(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `SDIO_SLC_FRHOST_BIT0_INT_ENA` field.</div>"]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit_int_ena(
        &mut self,
        n: u8,
    ) -> SDIO_SLC_FRHOST_BIT_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 8][n as usize];
        SDIO_SLC_FRHOST_BIT_INT_ENA_W::new(self, n)
    }
    #[doc = "Bit 0 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit0_int_ena(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_ENA_W::new(self, 0)
    }
    #[doc = "Bit 1 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit1_int_ena(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_ENA_W::new(self, 1)
    }
    #[doc = "Bit 2 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit2_int_ena(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_ENA_W::new(self, 2)
    }
    #[doc = "Bit 3 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit3_int_ena(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_ENA_W::new(self, 3)
    }
    #[doc = "Bit 4 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit4_int_ena(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_ENA_W::new(self, 4)
    }
    #[doc = "Bit 5 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit5_int_ena(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_ENA_W::new(self, 5)
    }
    #[doc = "Bit 6 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit6_int_ena(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_ENA_W::new(self, 6)
    }
    #[doc = "Bit 7 - Write 1 to enable interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit7_int_ena(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_ENA_W::new(self, 7)
    }
    #[doc = "Bit 8 - Write 1 to enable interrupt SLC0_RX_ENAART_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_enaart_int_ena(
        &mut self,
    ) -> SDIO_SLC0_RX_ENAART_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC0_RX_ENAART_INT_ENA_W::new(self, 8)
    }
    #[doc = "Bit 9 - Write 1 to enable interrupt SLC0_TX_ENAART_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_enaart_int_ena(
        &mut self,
    ) -> SDIO_SLC0_TX_ENAART_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC0_TX_ENAART_INT_ENA_W::new(self, 9)
    }
    #[doc = "Bit 10 - Write 1 to enable interrupt SLC0_RX_UDF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_udf_int_ena(&mut self) -> SDIO_SLC0_RX_UDF_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC0_RX_UDF_INT_ENA_W::new(self, 10)
    }
    #[doc = "Bit 11 - Write 1 to enable interrupt SLC0_TX_OVF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_ovf_int_ena(&mut self) -> SDIO_SLC0_TX_OVF_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC0_TX_OVF_INT_ENA_W::new(self, 11)
    }
    #[doc = "Bit 14 - Write 1 to enable interrupt SLC0_TX_DONE_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_done_int_ena(
        &mut self,
    ) -> SDIO_SLC0_TX_DONE_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC0_TX_DONE_INT_ENA_W::new(self, 14)
    }
    #[doc = "Bit 15 - Write 1 to enable interrupt SLC0_TX_SUC_EOF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_suc_eof_int_ena(
        &mut self,
    ) -> SDIO_SLC0_TX_SUC_EOF_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC0_TX_SUC_EOF_INT_ENA_W::new(self, 15)
    }
    #[doc = "Bit 16 - Write 1 to enable interrupt SLC0_RX_DONE_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_done_int_ena(
        &mut self,
    ) -> SDIO_SLC0_RX_DONE_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC0_RX_DONE_INT_ENA_W::new(self, 16)
    }
    #[doc = "Bit 17 - Write 1 to enable interrupt SLC0_RX_EOF_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_eof_int_ena(&mut self) -> SDIO_SLC0_RX_EOF_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC0_RX_EOF_INT_ENA_W::new(self, 17)
    }
    #[doc = "Bit 19 - Write 1 to enable interrupt SLC0_TX_DSCR_ERR_INT."]
    #[inline(always)]
    pub fn sdio_slc0_tx_dscr_err_int_ena(
        &mut self,
    ) -> SDIO_SLC0_TX_DSCR_ERR_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC0_TX_DSCR_ERR_INT_ENA_W::new(self, 19)
    }
    #[doc = "Bit 20 - Write 1 to enable interrupt SLC0_RX_DSCR_ERR_INT."]
    #[inline(always)]
    pub fn sdio_slc0_rx_dscr_err_int_ena(
        &mut self,
    ) -> SDIO_SLC0_RX_DSCR_ERR_INT_ENA_W<'_, SLC0INT_ENA_SPEC> {
        SDIO_SLC0_RX_DSCR_ERR_INT_ENA_W::new(self, 20)
    }
}
#[doc = "SLC0 to slave interrupt enable\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0int_ena::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0int_ena::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC0INT_ENA_SPEC;
impl crate::RegisterSpec for SLC0INT_ENA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc0int_ena::R`](R) reader structure"]
impl crate::Readable for SLC0INT_ENA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slc0int_ena::W`](W) writer structure"]
impl crate::Writable for SLC0INT_ENA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC0INT_ENA to value 0"]
impl crate::Resettable for SLC0INT_ENA_SPEC {}
