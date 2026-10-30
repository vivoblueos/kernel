#[doc = "Register `INT_ENA` reader"]
pub type R = crate::R<INT_ENA_SPEC>;
#[doc = "Register `INT_ENA` writer"]
pub type W = crate::W<INT_ENA_SPEC>;
#[doc = "Field `RXFIFO_FULL` reader - This is the enable bit for rxfifo_full_int_st register."]
pub type RXFIFO_FULL_R = crate::BitReader;
#[doc = "Field `RXFIFO_FULL` writer - This is the enable bit for rxfifo_full_int_st register."]
pub type RXFIFO_FULL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TXFIFO_EMPTY` reader - This is the enable bit for txfifo_empty_int_st register."]
pub type TXFIFO_EMPTY_R = crate::BitReader;
#[doc = "Field `TXFIFO_EMPTY` writer - This is the enable bit for txfifo_empty_int_st register."]
pub type TXFIFO_EMPTY_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PARITY_ERR` reader - This is the enable bit for parity_err_int_st register."]
pub type PARITY_ERR_R = crate::BitReader;
#[doc = "Field `PARITY_ERR` writer - This is the enable bit for parity_err_int_st register."]
pub type PARITY_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FRM_ERR` reader - This is the enable bit for frm_err_int_st register."]
pub type FRM_ERR_R = crate::BitReader;
#[doc = "Field `FRM_ERR` writer - This is the enable bit for frm_err_int_st register."]
pub type FRM_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXFIFO_OVF` reader - This is the enable bit for rxfifo_ovf_int_st register."]
pub type RXFIFO_OVF_R = crate::BitReader;
#[doc = "Field `RXFIFO_OVF` writer - This is the enable bit for rxfifo_ovf_int_st register."]
pub type RXFIFO_OVF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DSR_CHG` reader - This is the enable bit for dsr_chg_int_st register."]
pub type DSR_CHG_R = crate::BitReader;
#[doc = "Field `DSR_CHG` writer - This is the enable bit for dsr_chg_int_st register."]
pub type DSR_CHG_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CTS_CHG` reader - This is the enable bit for cts_chg_int_st register."]
pub type CTS_CHG_R = crate::BitReader;
#[doc = "Field `CTS_CHG` writer - This is the enable bit for cts_chg_int_st register."]
pub type CTS_CHG_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BRK_DET` reader - This is the enable bit for brk_det_int_st register."]
pub type BRK_DET_R = crate::BitReader;
#[doc = "Field `BRK_DET` writer - This is the enable bit for brk_det_int_st register."]
pub type BRK_DET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXFIFO_TOUT` reader - This is the enable bit for rxfifo_tout_int_st register."]
pub type RXFIFO_TOUT_R = crate::BitReader;
#[doc = "Field `RXFIFO_TOUT` writer - This is the enable bit for rxfifo_tout_int_st register."]
pub type RXFIFO_TOUT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SW_XON` reader - This is the enable bit for sw_xon_int_st register."]
pub type SW_XON_R = crate::BitReader;
#[doc = "Field `SW_XON` writer - This is the enable bit for sw_xon_int_st register."]
pub type SW_XON_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SW_XOFF` reader - This is the enable bit for sw_xoff_int_st register."]
pub type SW_XOFF_R = crate::BitReader;
#[doc = "Field `SW_XOFF` writer - This is the enable bit for sw_xoff_int_st register."]
pub type SW_XOFF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GLITCH_DET` reader - This is the enable bit for glitch_det_int_st register."]
pub type GLITCH_DET_R = crate::BitReader;
#[doc = "Field `GLITCH_DET` writer - This is the enable bit for glitch_det_int_st register."]
pub type GLITCH_DET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_BRK_DONE` reader - This is the enable bit for tx_brk_done_int_st register."]
pub type TX_BRK_DONE_R = crate::BitReader;
#[doc = "Field `TX_BRK_DONE` writer - This is the enable bit for tx_brk_done_int_st register."]
pub type TX_BRK_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_BRK_IDLE_DONE` reader - This is the enable bit for tx_brk_idle_done_int_st register."]
pub type TX_BRK_IDLE_DONE_R = crate::BitReader;
#[doc = "Field `TX_BRK_IDLE_DONE` writer - This is the enable bit for tx_brk_idle_done_int_st register."]
pub type TX_BRK_IDLE_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_DONE` reader - This is the enable bit for tx_done_int_st register."]
pub type TX_DONE_R = crate::BitReader;
#[doc = "Field `TX_DONE` writer - This is the enable bit for tx_done_int_st register."]
pub type TX_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AT_CMD_CHAR_DET` reader - This is the enable bit for at_cmd_char_det_int_st register."]
pub type AT_CMD_CHAR_DET_R = crate::BitReader;
#[doc = "Field `AT_CMD_CHAR_DET` writer - This is the enable bit for at_cmd_char_det_int_st register."]
pub type AT_CMD_CHAR_DET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WAKEUP` reader - This is the enable bit for uart_wakeup_int_st register."]
pub type WAKEUP_R = crate::BitReader;
#[doc = "Field `WAKEUP` writer - This is the enable bit for uart_wakeup_int_st register."]
pub type WAKEUP_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - This is the enable bit for rxfifo_full_int_st register."]
    #[inline(always)]
    pub fn rxfifo_full(&self) -> RXFIFO_FULL_R {
        RXFIFO_FULL_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - This is the enable bit for txfifo_empty_int_st register."]
    #[inline(always)]
    pub fn txfifo_empty(&self) -> TXFIFO_EMPTY_R {
        TXFIFO_EMPTY_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - This is the enable bit for parity_err_int_st register."]
    #[inline(always)]
    pub fn parity_err(&self) -> PARITY_ERR_R {
        PARITY_ERR_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - This is the enable bit for frm_err_int_st register."]
    #[inline(always)]
    pub fn frm_err(&self) -> FRM_ERR_R {
        FRM_ERR_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - This is the enable bit for rxfifo_ovf_int_st register."]
    #[inline(always)]
    pub fn rxfifo_ovf(&self) -> RXFIFO_OVF_R {
        RXFIFO_OVF_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - This is the enable bit for dsr_chg_int_st register."]
    #[inline(always)]
    pub fn dsr_chg(&self) -> DSR_CHG_R {
        DSR_CHG_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - This is the enable bit for cts_chg_int_st register."]
    #[inline(always)]
    pub fn cts_chg(&self) -> CTS_CHG_R {
        CTS_CHG_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - This is the enable bit for brk_det_int_st register."]
    #[inline(always)]
    pub fn brk_det(&self) -> BRK_DET_R {
        BRK_DET_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - This is the enable bit for rxfifo_tout_int_st register."]
    #[inline(always)]
    pub fn rxfifo_tout(&self) -> RXFIFO_TOUT_R {
        RXFIFO_TOUT_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - This is the enable bit for sw_xon_int_st register."]
    #[inline(always)]
    pub fn sw_xon(&self) -> SW_XON_R {
        SW_XON_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - This is the enable bit for sw_xoff_int_st register."]
    #[inline(always)]
    pub fn sw_xoff(&self) -> SW_XOFF_R {
        SW_XOFF_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - This is the enable bit for glitch_det_int_st register."]
    #[inline(always)]
    pub fn glitch_det(&self) -> GLITCH_DET_R {
        GLITCH_DET_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - This is the enable bit for tx_brk_done_int_st register."]
    #[inline(always)]
    pub fn tx_brk_done(&self) -> TX_BRK_DONE_R {
        TX_BRK_DONE_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - This is the enable bit for tx_brk_idle_done_int_st register."]
    #[inline(always)]
    pub fn tx_brk_idle_done(&self) -> TX_BRK_IDLE_DONE_R {
        TX_BRK_IDLE_DONE_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - This is the enable bit for tx_done_int_st register."]
    #[inline(always)]
    pub fn tx_done(&self) -> TX_DONE_R {
        TX_DONE_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 18 - This is the enable bit for at_cmd_char_det_int_st register."]
    #[inline(always)]
    pub fn at_cmd_char_det(&self) -> AT_CMD_CHAR_DET_R {
        AT_CMD_CHAR_DET_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - This is the enable bit for uart_wakeup_int_st register."]
    #[inline(always)]
    pub fn wakeup(&self) -> WAKEUP_R {
        WAKEUP_R::new(((self.bits >> 19) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_ENA")
            .field("rxfifo_full", &self.rxfifo_full())
            .field("txfifo_empty", &self.txfifo_empty())
            .field("parity_err", &self.parity_err())
            .field("frm_err", &self.frm_err())
            .field("rxfifo_ovf", &self.rxfifo_ovf())
            .field("dsr_chg", &self.dsr_chg())
            .field("cts_chg", &self.cts_chg())
            .field("brk_det", &self.brk_det())
            .field("rxfifo_tout", &self.rxfifo_tout())
            .field("sw_xon", &self.sw_xon())
            .field("sw_xoff", &self.sw_xoff())
            .field("glitch_det", &self.glitch_det())
            .field("tx_brk_done", &self.tx_brk_done())
            .field("tx_brk_idle_done", &self.tx_brk_idle_done())
            .field("tx_done", &self.tx_done())
            .field("at_cmd_char_det", &self.at_cmd_char_det())
            .field("wakeup", &self.wakeup())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - This is the enable bit for rxfifo_full_int_st register."]
    #[inline(always)]
    pub fn rxfifo_full(&mut self) -> RXFIFO_FULL_W<'_, INT_ENA_SPEC> {
        RXFIFO_FULL_W::new(self, 0)
    }
    #[doc = "Bit 1 - This is the enable bit for txfifo_empty_int_st register."]
    #[inline(always)]
    pub fn txfifo_empty(&mut self) -> TXFIFO_EMPTY_W<'_, INT_ENA_SPEC> {
        TXFIFO_EMPTY_W::new(self, 1)
    }
    #[doc = "Bit 2 - This is the enable bit for parity_err_int_st register."]
    #[inline(always)]
    pub fn parity_err(&mut self) -> PARITY_ERR_W<'_, INT_ENA_SPEC> {
        PARITY_ERR_W::new(self, 2)
    }
    #[doc = "Bit 3 - This is the enable bit for frm_err_int_st register."]
    #[inline(always)]
    pub fn frm_err(&mut self) -> FRM_ERR_W<'_, INT_ENA_SPEC> {
        FRM_ERR_W::new(self, 3)
    }
    #[doc = "Bit 4 - This is the enable bit for rxfifo_ovf_int_st register."]
    #[inline(always)]
    pub fn rxfifo_ovf(&mut self) -> RXFIFO_OVF_W<'_, INT_ENA_SPEC> {
        RXFIFO_OVF_W::new(self, 4)
    }
    #[doc = "Bit 5 - This is the enable bit for dsr_chg_int_st register."]
    #[inline(always)]
    pub fn dsr_chg(&mut self) -> DSR_CHG_W<'_, INT_ENA_SPEC> {
        DSR_CHG_W::new(self, 5)
    }
    #[doc = "Bit 6 - This is the enable bit for cts_chg_int_st register."]
    #[inline(always)]
    pub fn cts_chg(&mut self) -> CTS_CHG_W<'_, INT_ENA_SPEC> {
        CTS_CHG_W::new(self, 6)
    }
    #[doc = "Bit 7 - This is the enable bit for brk_det_int_st register."]
    #[inline(always)]
    pub fn brk_det(&mut self) -> BRK_DET_W<'_, INT_ENA_SPEC> {
        BRK_DET_W::new(self, 7)
    }
    #[doc = "Bit 8 - This is the enable bit for rxfifo_tout_int_st register."]
    #[inline(always)]
    pub fn rxfifo_tout(&mut self) -> RXFIFO_TOUT_W<'_, INT_ENA_SPEC> {
        RXFIFO_TOUT_W::new(self, 8)
    }
    #[doc = "Bit 9 - This is the enable bit for sw_xon_int_st register."]
    #[inline(always)]
    pub fn sw_xon(&mut self) -> SW_XON_W<'_, INT_ENA_SPEC> {
        SW_XON_W::new(self, 9)
    }
    #[doc = "Bit 10 - This is the enable bit for sw_xoff_int_st register."]
    #[inline(always)]
    pub fn sw_xoff(&mut self) -> SW_XOFF_W<'_, INT_ENA_SPEC> {
        SW_XOFF_W::new(self, 10)
    }
    #[doc = "Bit 11 - This is the enable bit for glitch_det_int_st register."]
    #[inline(always)]
    pub fn glitch_det(&mut self) -> GLITCH_DET_W<'_, INT_ENA_SPEC> {
        GLITCH_DET_W::new(self, 11)
    }
    #[doc = "Bit 12 - This is the enable bit for tx_brk_done_int_st register."]
    #[inline(always)]
    pub fn tx_brk_done(&mut self) -> TX_BRK_DONE_W<'_, INT_ENA_SPEC> {
        TX_BRK_DONE_W::new(self, 12)
    }
    #[doc = "Bit 13 - This is the enable bit for tx_brk_idle_done_int_st register."]
    #[inline(always)]
    pub fn tx_brk_idle_done(&mut self) -> TX_BRK_IDLE_DONE_W<'_, INT_ENA_SPEC> {
        TX_BRK_IDLE_DONE_W::new(self, 13)
    }
    #[doc = "Bit 14 - This is the enable bit for tx_done_int_st register."]
    #[inline(always)]
    pub fn tx_done(&mut self) -> TX_DONE_W<'_, INT_ENA_SPEC> {
        TX_DONE_W::new(self, 14)
    }
    #[doc = "Bit 18 - This is the enable bit for at_cmd_char_det_int_st register."]
    #[inline(always)]
    pub fn at_cmd_char_det(&mut self) -> AT_CMD_CHAR_DET_W<'_, INT_ENA_SPEC> {
        AT_CMD_CHAR_DET_W::new(self, 18)
    }
    #[doc = "Bit 19 - This is the enable bit for uart_wakeup_int_st register."]
    #[inline(always)]
    pub fn wakeup(&mut self) -> WAKEUP_W<'_, INT_ENA_SPEC> {
        WAKEUP_W::new(self, 19)
    }
}
#[doc = "Interrupt enable bits\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_ENA_SPEC;
impl crate::RegisterSpec for INT_ENA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_ena::R`](R) reader structure"]
impl crate::Readable for INT_ENA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`int_ena::W`](W) writer structure"]
impl crate::Writable for INT_ENA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_ENA to value 0"]
impl crate::Resettable for INT_ENA_SPEC {}
