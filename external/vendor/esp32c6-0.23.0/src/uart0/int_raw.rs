#[doc = "Register `INT_RAW` reader"]
pub type R = crate::R<INT_RAW_SPEC>;
#[doc = "Register `INT_RAW` writer"]
pub type W = crate::W<INT_RAW_SPEC>;
#[doc = "Field `RXFIFO_FULL` reader - This interrupt raw bit turns to high level when receiver receives more data than what rxfifo_full_thrhd specifies."]
pub type RXFIFO_FULL_R = crate::BitReader;
#[doc = "Field `RXFIFO_FULL` writer - This interrupt raw bit turns to high level when receiver receives more data than what rxfifo_full_thrhd specifies."]
pub type RXFIFO_FULL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TXFIFO_EMPTY` reader - This interrupt raw bit turns to high level when the amount of data in Tx-FIFO is less than what txfifo_empty_thrhd specifies ."]
pub type TXFIFO_EMPTY_R = crate::BitReader;
#[doc = "Field `TXFIFO_EMPTY` writer - This interrupt raw bit turns to high level when the amount of data in Tx-FIFO is less than what txfifo_empty_thrhd specifies ."]
pub type TXFIFO_EMPTY_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PARITY_ERR` reader - This interrupt raw bit turns to high level when receiver detects a parity error in the data."]
pub type PARITY_ERR_R = crate::BitReader;
#[doc = "Field `PARITY_ERR` writer - This interrupt raw bit turns to high level when receiver detects a parity error in the data."]
pub type PARITY_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FRM_ERR` reader - This interrupt raw bit turns to high level when receiver detects a data frame error ."]
pub type FRM_ERR_R = crate::BitReader;
#[doc = "Field `FRM_ERR` writer - This interrupt raw bit turns to high level when receiver detects a data frame error ."]
pub type FRM_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXFIFO_OVF` reader - This interrupt raw bit turns to high level when receiver receives more data than the FIFO can store."]
pub type RXFIFO_OVF_R = crate::BitReader;
#[doc = "Field `RXFIFO_OVF` writer - This interrupt raw bit turns to high level when receiver receives more data than the FIFO can store."]
pub type RXFIFO_OVF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DSR_CHG` reader - This interrupt raw bit turns to high level when receiver detects the edge change of DSRn signal."]
pub type DSR_CHG_R = crate::BitReader;
#[doc = "Field `DSR_CHG` writer - This interrupt raw bit turns to high level when receiver detects the edge change of DSRn signal."]
pub type DSR_CHG_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CTS_CHG` reader - This interrupt raw bit turns to high level when receiver detects the edge change of CTSn signal."]
pub type CTS_CHG_R = crate::BitReader;
#[doc = "Field `CTS_CHG` writer - This interrupt raw bit turns to high level when receiver detects the edge change of CTSn signal."]
pub type CTS_CHG_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BRK_DET` reader - This interrupt raw bit turns to high level when receiver detects a 0 after the stop bit."]
pub type BRK_DET_R = crate::BitReader;
#[doc = "Field `BRK_DET` writer - This interrupt raw bit turns to high level when receiver detects a 0 after the stop bit."]
pub type BRK_DET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXFIFO_TOUT` reader - This interrupt raw bit turns to high level when receiver takes more time than rx_tout_thrhd to receive a byte."]
pub type RXFIFO_TOUT_R = crate::BitReader;
#[doc = "Field `RXFIFO_TOUT` writer - This interrupt raw bit turns to high level when receiver takes more time than rx_tout_thrhd to receive a byte."]
pub type RXFIFO_TOUT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SW_XON` reader - This interrupt raw bit turns to high level when receiver recevies Xon char when uart_sw_flow_con_en is set to 1."]
pub type SW_XON_R = crate::BitReader;
#[doc = "Field `SW_XON` writer - This interrupt raw bit turns to high level when receiver recevies Xon char when uart_sw_flow_con_en is set to 1."]
pub type SW_XON_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SW_XOFF` reader - This interrupt raw bit turns to high level when receiver receives Xoff char when uart_sw_flow_con_en is set to 1."]
pub type SW_XOFF_R = crate::BitReader;
#[doc = "Field `SW_XOFF` writer - This interrupt raw bit turns to high level when receiver receives Xoff char when uart_sw_flow_con_en is set to 1."]
pub type SW_XOFF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GLITCH_DET` reader - This interrupt raw bit turns to high level when receiver detects a glitch in the middle of a start bit."]
pub type GLITCH_DET_R = crate::BitReader;
#[doc = "Field `GLITCH_DET` writer - This interrupt raw bit turns to high level when receiver detects a glitch in the middle of a start bit."]
pub type GLITCH_DET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_BRK_DONE` reader - This interrupt raw bit turns to high level when transmitter completes sending NULL characters after all data in Tx-FIFO are sent."]
pub type TX_BRK_DONE_R = crate::BitReader;
#[doc = "Field `TX_BRK_DONE` writer - This interrupt raw bit turns to high level when transmitter completes sending NULL characters after all data in Tx-FIFO are sent."]
pub type TX_BRK_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_BRK_IDLE_DONE` reader - This interrupt raw bit turns to high level when transmitter has kept the shortest duration after sending the last data."]
pub type TX_BRK_IDLE_DONE_R = crate::BitReader;
#[doc = "Field `TX_BRK_IDLE_DONE` writer - This interrupt raw bit turns to high level when transmitter has kept the shortest duration after sending the last data."]
pub type TX_BRK_IDLE_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_DONE` reader - This interrupt raw bit turns to high level when transmitter has send out all data in FIFO."]
pub type TX_DONE_R = crate::BitReader;
#[doc = "Field `TX_DONE` writer - This interrupt raw bit turns to high level when transmitter has send out all data in FIFO."]
pub type TX_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RS485_PARITY_ERR` reader - This interrupt raw bit turns to high level when receiver detects a parity error from the echo of transmitter in rs485 mode."]
pub type RS485_PARITY_ERR_R = crate::BitReader;
#[doc = "Field `RS485_PARITY_ERR` writer - This interrupt raw bit turns to high level when receiver detects a parity error from the echo of transmitter in rs485 mode."]
pub type RS485_PARITY_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RS485_FRM_ERR` reader - This interrupt raw bit turns to high level when receiver detects a data frame error from the echo of transmitter in rs485 mode."]
pub type RS485_FRM_ERR_R = crate::BitReader;
#[doc = "Field `RS485_FRM_ERR` writer - This interrupt raw bit turns to high level when receiver detects a data frame error from the echo of transmitter in rs485 mode."]
pub type RS485_FRM_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RS485_CLASH` reader - This interrupt raw bit turns to high level when detects a clash between transmitter and receiver in rs485 mode."]
pub type RS485_CLASH_R = crate::BitReader;
#[doc = "Field `RS485_CLASH` writer - This interrupt raw bit turns to high level when detects a clash between transmitter and receiver in rs485 mode."]
pub type RS485_CLASH_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AT_CMD_CHAR_DET` reader - This interrupt raw bit turns to high level when receiver detects the configured at_cmd char."]
pub type AT_CMD_CHAR_DET_R = crate::BitReader;
#[doc = "Field `AT_CMD_CHAR_DET` writer - This interrupt raw bit turns to high level when receiver detects the configured at_cmd char."]
pub type AT_CMD_CHAR_DET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WAKEUP` reader - This interrupt raw bit turns to high level when input rxd edge changes more times than what reg_active_threshold specifies in light sleeping mode."]
pub type WAKEUP_R = crate::BitReader;
#[doc = "Field `WAKEUP` writer - This interrupt raw bit turns to high level when input rxd edge changes more times than what reg_active_threshold specifies in light sleeping mode."]
pub type WAKEUP_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - This interrupt raw bit turns to high level when receiver receives more data than what rxfifo_full_thrhd specifies."]
    #[inline(always)]
    pub fn rxfifo_full(&self) -> RXFIFO_FULL_R {
        RXFIFO_FULL_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - This interrupt raw bit turns to high level when the amount of data in Tx-FIFO is less than what txfifo_empty_thrhd specifies ."]
    #[inline(always)]
    pub fn txfifo_empty(&self) -> TXFIFO_EMPTY_R {
        TXFIFO_EMPTY_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - This interrupt raw bit turns to high level when receiver detects a parity error in the data."]
    #[inline(always)]
    pub fn parity_err(&self) -> PARITY_ERR_R {
        PARITY_ERR_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - This interrupt raw bit turns to high level when receiver detects a data frame error ."]
    #[inline(always)]
    pub fn frm_err(&self) -> FRM_ERR_R {
        FRM_ERR_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - This interrupt raw bit turns to high level when receiver receives more data than the FIFO can store."]
    #[inline(always)]
    pub fn rxfifo_ovf(&self) -> RXFIFO_OVF_R {
        RXFIFO_OVF_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - This interrupt raw bit turns to high level when receiver detects the edge change of DSRn signal."]
    #[inline(always)]
    pub fn dsr_chg(&self) -> DSR_CHG_R {
        DSR_CHG_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - This interrupt raw bit turns to high level when receiver detects the edge change of CTSn signal."]
    #[inline(always)]
    pub fn cts_chg(&self) -> CTS_CHG_R {
        CTS_CHG_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - This interrupt raw bit turns to high level when receiver detects a 0 after the stop bit."]
    #[inline(always)]
    pub fn brk_det(&self) -> BRK_DET_R {
        BRK_DET_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - This interrupt raw bit turns to high level when receiver takes more time than rx_tout_thrhd to receive a byte."]
    #[inline(always)]
    pub fn rxfifo_tout(&self) -> RXFIFO_TOUT_R {
        RXFIFO_TOUT_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - This interrupt raw bit turns to high level when receiver recevies Xon char when uart_sw_flow_con_en is set to 1."]
    #[inline(always)]
    pub fn sw_xon(&self) -> SW_XON_R {
        SW_XON_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - This interrupt raw bit turns to high level when receiver receives Xoff char when uart_sw_flow_con_en is set to 1."]
    #[inline(always)]
    pub fn sw_xoff(&self) -> SW_XOFF_R {
        SW_XOFF_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - This interrupt raw bit turns to high level when receiver detects a glitch in the middle of a start bit."]
    #[inline(always)]
    pub fn glitch_det(&self) -> GLITCH_DET_R {
        GLITCH_DET_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - This interrupt raw bit turns to high level when transmitter completes sending NULL characters after all data in Tx-FIFO are sent."]
    #[inline(always)]
    pub fn tx_brk_done(&self) -> TX_BRK_DONE_R {
        TX_BRK_DONE_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - This interrupt raw bit turns to high level when transmitter has kept the shortest duration after sending the last data."]
    #[inline(always)]
    pub fn tx_brk_idle_done(&self) -> TX_BRK_IDLE_DONE_R {
        TX_BRK_IDLE_DONE_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - This interrupt raw bit turns to high level when transmitter has send out all data in FIFO."]
    #[inline(always)]
    pub fn tx_done(&self) -> TX_DONE_R {
        TX_DONE_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - This interrupt raw bit turns to high level when receiver detects a parity error from the echo of transmitter in rs485 mode."]
    #[inline(always)]
    pub fn rs485_parity_err(&self) -> RS485_PARITY_ERR_R {
        RS485_PARITY_ERR_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - This interrupt raw bit turns to high level when receiver detects a data frame error from the echo of transmitter in rs485 mode."]
    #[inline(always)]
    pub fn rs485_frm_err(&self) -> RS485_FRM_ERR_R {
        RS485_FRM_ERR_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - This interrupt raw bit turns to high level when detects a clash between transmitter and receiver in rs485 mode."]
    #[inline(always)]
    pub fn rs485_clash(&self) -> RS485_CLASH_R {
        RS485_CLASH_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - This interrupt raw bit turns to high level when receiver detects the configured at_cmd char."]
    #[inline(always)]
    pub fn at_cmd_char_det(&self) -> AT_CMD_CHAR_DET_R {
        AT_CMD_CHAR_DET_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - This interrupt raw bit turns to high level when input rxd edge changes more times than what reg_active_threshold specifies in light sleeping mode."]
    #[inline(always)]
    pub fn wakeup(&self) -> WAKEUP_R {
        WAKEUP_R::new(((self.bits >> 19) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_RAW")
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
            .field("rs485_parity_err", &self.rs485_parity_err())
            .field("rs485_frm_err", &self.rs485_frm_err())
            .field("rs485_clash", &self.rs485_clash())
            .field("at_cmd_char_det", &self.at_cmd_char_det())
            .field("wakeup", &self.wakeup())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - This interrupt raw bit turns to high level when receiver receives more data than what rxfifo_full_thrhd specifies."]
    #[inline(always)]
    pub fn rxfifo_full(&mut self) -> RXFIFO_FULL_W<'_, INT_RAW_SPEC> {
        RXFIFO_FULL_W::new(self, 0)
    }
    #[doc = "Bit 1 - This interrupt raw bit turns to high level when the amount of data in Tx-FIFO is less than what txfifo_empty_thrhd specifies ."]
    #[inline(always)]
    pub fn txfifo_empty(&mut self) -> TXFIFO_EMPTY_W<'_, INT_RAW_SPEC> {
        TXFIFO_EMPTY_W::new(self, 1)
    }
    #[doc = "Bit 2 - This interrupt raw bit turns to high level when receiver detects a parity error in the data."]
    #[inline(always)]
    pub fn parity_err(&mut self) -> PARITY_ERR_W<'_, INT_RAW_SPEC> {
        PARITY_ERR_W::new(self, 2)
    }
    #[doc = "Bit 3 - This interrupt raw bit turns to high level when receiver detects a data frame error ."]
    #[inline(always)]
    pub fn frm_err(&mut self) -> FRM_ERR_W<'_, INT_RAW_SPEC> {
        FRM_ERR_W::new(self, 3)
    }
    #[doc = "Bit 4 - This interrupt raw bit turns to high level when receiver receives more data than the FIFO can store."]
    #[inline(always)]
    pub fn rxfifo_ovf(&mut self) -> RXFIFO_OVF_W<'_, INT_RAW_SPEC> {
        RXFIFO_OVF_W::new(self, 4)
    }
    #[doc = "Bit 5 - This interrupt raw bit turns to high level when receiver detects the edge change of DSRn signal."]
    #[inline(always)]
    pub fn dsr_chg(&mut self) -> DSR_CHG_W<'_, INT_RAW_SPEC> {
        DSR_CHG_W::new(self, 5)
    }
    #[doc = "Bit 6 - This interrupt raw bit turns to high level when receiver detects the edge change of CTSn signal."]
    #[inline(always)]
    pub fn cts_chg(&mut self) -> CTS_CHG_W<'_, INT_RAW_SPEC> {
        CTS_CHG_W::new(self, 6)
    }
    #[doc = "Bit 7 - This interrupt raw bit turns to high level when receiver detects a 0 after the stop bit."]
    #[inline(always)]
    pub fn brk_det(&mut self) -> BRK_DET_W<'_, INT_RAW_SPEC> {
        BRK_DET_W::new(self, 7)
    }
    #[doc = "Bit 8 - This interrupt raw bit turns to high level when receiver takes more time than rx_tout_thrhd to receive a byte."]
    #[inline(always)]
    pub fn rxfifo_tout(&mut self) -> RXFIFO_TOUT_W<'_, INT_RAW_SPEC> {
        RXFIFO_TOUT_W::new(self, 8)
    }
    #[doc = "Bit 9 - This interrupt raw bit turns to high level when receiver recevies Xon char when uart_sw_flow_con_en is set to 1."]
    #[inline(always)]
    pub fn sw_xon(&mut self) -> SW_XON_W<'_, INT_RAW_SPEC> {
        SW_XON_W::new(self, 9)
    }
    #[doc = "Bit 10 - This interrupt raw bit turns to high level when receiver receives Xoff char when uart_sw_flow_con_en is set to 1."]
    #[inline(always)]
    pub fn sw_xoff(&mut self) -> SW_XOFF_W<'_, INT_RAW_SPEC> {
        SW_XOFF_W::new(self, 10)
    }
    #[doc = "Bit 11 - This interrupt raw bit turns to high level when receiver detects a glitch in the middle of a start bit."]
    #[inline(always)]
    pub fn glitch_det(&mut self) -> GLITCH_DET_W<'_, INT_RAW_SPEC> {
        GLITCH_DET_W::new(self, 11)
    }
    #[doc = "Bit 12 - This interrupt raw bit turns to high level when transmitter completes sending NULL characters after all data in Tx-FIFO are sent."]
    #[inline(always)]
    pub fn tx_brk_done(&mut self) -> TX_BRK_DONE_W<'_, INT_RAW_SPEC> {
        TX_BRK_DONE_W::new(self, 12)
    }
    #[doc = "Bit 13 - This interrupt raw bit turns to high level when transmitter has kept the shortest duration after sending the last data."]
    #[inline(always)]
    pub fn tx_brk_idle_done(&mut self) -> TX_BRK_IDLE_DONE_W<'_, INT_RAW_SPEC> {
        TX_BRK_IDLE_DONE_W::new(self, 13)
    }
    #[doc = "Bit 14 - This interrupt raw bit turns to high level when transmitter has send out all data in FIFO."]
    #[inline(always)]
    pub fn tx_done(&mut self) -> TX_DONE_W<'_, INT_RAW_SPEC> {
        TX_DONE_W::new(self, 14)
    }
    #[doc = "Bit 15 - This interrupt raw bit turns to high level when receiver detects a parity error from the echo of transmitter in rs485 mode."]
    #[inline(always)]
    pub fn rs485_parity_err(&mut self) -> RS485_PARITY_ERR_W<'_, INT_RAW_SPEC> {
        RS485_PARITY_ERR_W::new(self, 15)
    }
    #[doc = "Bit 16 - This interrupt raw bit turns to high level when receiver detects a data frame error from the echo of transmitter in rs485 mode."]
    #[inline(always)]
    pub fn rs485_frm_err(&mut self) -> RS485_FRM_ERR_W<'_, INT_RAW_SPEC> {
        RS485_FRM_ERR_W::new(self, 16)
    }
    #[doc = "Bit 17 - This interrupt raw bit turns to high level when detects a clash between transmitter and receiver in rs485 mode."]
    #[inline(always)]
    pub fn rs485_clash(&mut self) -> RS485_CLASH_W<'_, INT_RAW_SPEC> {
        RS485_CLASH_W::new(self, 17)
    }
    #[doc = "Bit 18 - This interrupt raw bit turns to high level when receiver detects the configured at_cmd char."]
    #[inline(always)]
    pub fn at_cmd_char_det(&mut self) -> AT_CMD_CHAR_DET_W<'_, INT_RAW_SPEC> {
        AT_CMD_CHAR_DET_W::new(self, 18)
    }
    #[doc = "Bit 19 - This interrupt raw bit turns to high level when input rxd edge changes more times than what reg_active_threshold specifies in light sleeping mode."]
    #[inline(always)]
    pub fn wakeup(&mut self) -> WAKEUP_W<'_, INT_RAW_SPEC> {
        WAKEUP_W::new(self, 19)
    }
}
#[doc = "Raw interrupt status\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_raw::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_RAW_SPEC;
impl crate::RegisterSpec for INT_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_raw::R`](R) reader structure"]
impl crate::Readable for INT_RAW_SPEC {}
#[doc = "`write(|w| ..)` method takes [`int_raw::W`](W) writer structure"]
impl crate::Writable for INT_RAW_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_RAW to value 0x02"]
impl crate::Resettable for INT_RAW_SPEC {
    const RESET_VALUE: u32 = 0x02;
}
