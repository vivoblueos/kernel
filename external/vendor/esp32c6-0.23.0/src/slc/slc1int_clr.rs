#[doc = "Register `SLC1INT_CLR` writer"]
pub type W = crate::W<SLC1INT_CLR_SPEC>;
#[doc = "Field `SDIO_SLC_FRHOST_BIT_INT_CLR(0-7)` writer - Write 1 to clear interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
pub type SDIO_SLC_FRHOST_BIT_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RX_CLRART_INT_CLR` writer - Write 1 to clear interrupt SLC1_RX_CLRART_INT."]
pub type SDIO_SLC1_RX_CLRART_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_TX_CLRART_INT_CLR` writer - Write 1 to clear interrupt SLC1_TX_CLRART_INT."]
pub type SDIO_SLC1_TX_CLRART_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RX_UDF_INT_CLR` writer - Write 1 to clear interrupt SLC1_RX_UDF_INT."]
pub type SDIO_SLC1_RX_UDF_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_TX_OVF_INT_CLR` writer - Write 1 to clear interrupt SLC1_TX_OVF_INT."]
pub type SDIO_SLC1_TX_OVF_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_TX_DONE_INT_CLR` writer - Write 1 to clear interrupt SLC1_TX_DONE_INT."]
pub type SDIO_SLC1_TX_DONE_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_TX_SUC_EOF_INT_CLR` writer - Write 1 to clear interrupt SLC1_TX_SUC_EOF_INT."]
pub type SDIO_SLC1_TX_SUC_EOF_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RX_DONE_INT_CLR` writer - Write 1 to clear interrupt SLC1_RX_DONE_INT."]
pub type SDIO_SLC1_RX_DONE_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RX_EOF_INT_CLR` writer - Write 1 to clear interrupt SLC1_RX_EOF_INT."]
pub type SDIO_SLC1_RX_EOF_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_TX_DSCR_ERR_INT_CLR` writer - Write 1 to clear interrupt SLC1_TX_DSCR_ERR_INT."]
pub type SDIO_SLC1_TX_DSCR_ERR_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC1_RX_DSCR_ERR_INT_CLR` writer - Write 1 to clear interrupt SLC1_RX_DSCR_ERR_INT."]
pub type SDIO_SLC1_RX_DSCR_ERR_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SLC1INT_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Write 1 to clear interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `SDIO_SLC_FRHOST_BIT0_INT_CLR` field.</div>"]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit_int_clr(
        &mut self,
        n: u8,
    ) -> SDIO_SLC_FRHOST_BIT_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 8][n as usize];
        SDIO_SLC_FRHOST_BIT_INT_CLR_W::new(self, n)
    }
    #[doc = "Bit 0 - Write 1 to clear interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit0_int_clr(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_CLR_W::new(self, 0)
    }
    #[doc = "Bit 1 - Write 1 to clear interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit1_int_clr(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_CLR_W::new(self, 1)
    }
    #[doc = "Bit 2 - Write 1 to clear interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit2_int_clr(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_CLR_W::new(self, 2)
    }
    #[doc = "Bit 3 - Write 1 to clear interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit3_int_clr(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_CLR_W::new(self, 3)
    }
    #[doc = "Bit 4 - Write 1 to clear interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit4_int_clr(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_CLR_W::new(self, 4)
    }
    #[doc = "Bit 5 - Write 1 to clear interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit5_int_clr(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_CLR_W::new(self, 5)
    }
    #[doc = "Bit 6 - Write 1 to clear interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit6_int_clr(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_CLR_W::new(self, 6)
    }
    #[doc = "Bit 7 - Write 1 to clear interrupt SLC_FRHOST_BITn_INT (n: 0-7)."]
    #[inline(always)]
    pub fn sdio_slc_frhost_bit7_int_clr(
        &mut self,
    ) -> SDIO_SLC_FRHOST_BIT_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC_FRHOST_BIT_INT_CLR_W::new(self, 7)
    }
    #[doc = "Bit 8 - Write 1 to clear interrupt SLC1_RX_CLRART_INT."]
    #[inline(always)]
    pub fn sdio_slc1_rx_clrart_int_clr(
        &mut self,
    ) -> SDIO_SLC1_RX_CLRART_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC1_RX_CLRART_INT_CLR_W::new(self, 8)
    }
    #[doc = "Bit 9 - Write 1 to clear interrupt SLC1_TX_CLRART_INT."]
    #[inline(always)]
    pub fn sdio_slc1_tx_clrart_int_clr(
        &mut self,
    ) -> SDIO_SLC1_TX_CLRART_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC1_TX_CLRART_INT_CLR_W::new(self, 9)
    }
    #[doc = "Bit 10 - Write 1 to clear interrupt SLC1_RX_UDF_INT."]
    #[inline(always)]
    pub fn sdio_slc1_rx_udf_int_clr(&mut self) -> SDIO_SLC1_RX_UDF_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC1_RX_UDF_INT_CLR_W::new(self, 10)
    }
    #[doc = "Bit 11 - Write 1 to clear interrupt SLC1_TX_OVF_INT."]
    #[inline(always)]
    pub fn sdio_slc1_tx_ovf_int_clr(&mut self) -> SDIO_SLC1_TX_OVF_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC1_TX_OVF_INT_CLR_W::new(self, 11)
    }
    #[doc = "Bit 14 - Write 1 to clear interrupt SLC1_TX_DONE_INT."]
    #[inline(always)]
    pub fn sdio_slc1_tx_done_int_clr(
        &mut self,
    ) -> SDIO_SLC1_TX_DONE_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC1_TX_DONE_INT_CLR_W::new(self, 14)
    }
    #[doc = "Bit 15 - Write 1 to clear interrupt SLC1_TX_SUC_EOF_INT."]
    #[inline(always)]
    pub fn sdio_slc1_tx_suc_eof_int_clr(
        &mut self,
    ) -> SDIO_SLC1_TX_SUC_EOF_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC1_TX_SUC_EOF_INT_CLR_W::new(self, 15)
    }
    #[doc = "Bit 16 - Write 1 to clear interrupt SLC1_RX_DONE_INT."]
    #[inline(always)]
    pub fn sdio_slc1_rx_done_int_clr(
        &mut self,
    ) -> SDIO_SLC1_RX_DONE_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC1_RX_DONE_INT_CLR_W::new(self, 16)
    }
    #[doc = "Bit 17 - Write 1 to clear interrupt SLC1_RX_EOF_INT."]
    #[inline(always)]
    pub fn sdio_slc1_rx_eof_int_clr(&mut self) -> SDIO_SLC1_RX_EOF_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC1_RX_EOF_INT_CLR_W::new(self, 17)
    }
    #[doc = "Bit 19 - Write 1 to clear interrupt SLC1_TX_DSCR_ERR_INT."]
    #[inline(always)]
    pub fn sdio_slc1_tx_dscr_err_int_clr(
        &mut self,
    ) -> SDIO_SLC1_TX_DSCR_ERR_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC1_TX_DSCR_ERR_INT_CLR_W::new(self, 19)
    }
    #[doc = "Bit 20 - Write 1 to clear interrupt SLC1_RX_DSCR_ERR_INT."]
    #[inline(always)]
    pub fn sdio_slc1_rx_dscr_err_int_clr(
        &mut self,
    ) -> SDIO_SLC1_RX_DSCR_ERR_INT_CLR_W<'_, SLC1INT_CLR_SPEC> {
        SDIO_SLC1_RX_DSCR_ERR_INT_CLR_W::new(self, 20)
    }
}
#[doc = "SLC1 to slave interrupt clear\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1int_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC1INT_CLR_SPEC;
impl crate::RegisterSpec for SLC1INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`slc1int_clr::W`](W) writer structure"]
impl crate::Writable for SLC1INT_CLR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC1INT_CLR to value 0"]
impl crate::Resettable for SLC1INT_CLR_SPEC {}
