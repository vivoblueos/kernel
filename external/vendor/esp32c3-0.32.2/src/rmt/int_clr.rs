#[doc = "Register `INT_CLR` writer"]
pub type W = crate::W<INT_CLR_SPEC>;
#[doc = "Field `CH_TX_END(0-1)` writer - reg_ch%s_tx_end_int_clr."]
pub type CH_TX_END_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH_RX_END(2-3)` writer - reg_ch%s_rx_end_int_clr."]
pub type CH_RX_END_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH_TX_ERR(0-1)` writer - reg_ch%s_err_int_clr."]
pub type CH_TX_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH_RX_ERR(2-3)` writer - reg_ch%s_err_int_clr."]
pub type CH_RX_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH_TX_THR_EVENT(0-1)` writer - reg_ch%s_tx_thr_event_int_clr."]
pub type CH_TX_THR_EVENT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH_RX_THR_EVENT(2-3)` writer - reg_ch%s_rx_thr_event_int_clr."]
pub type CH_RX_THR_EVENT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH_TX_LOOP(0-1)` writer - reg_ch%s_tx_loop_int_clr."]
pub type CH_TX_LOOP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<INT_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "reg_ch(0-1)_tx_end_int_clr."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH0_TX_END` field.</div>"]
    #[inline(always)]
    pub fn ch_tx_end(&mut self, n: u8) -> CH_TX_END_W<'_, INT_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 2][n as usize];
        CH_TX_END_W::new(self, n)
    }
    #[doc = "Bit 0 - reg_ch0_tx_end_int_clr."]
    #[inline(always)]
    pub fn ch0_tx_end(&mut self) -> CH_TX_END_W<'_, INT_CLR_SPEC> {
        CH_TX_END_W::new(self, 0)
    }
    #[doc = "Bit 1 - reg_ch1_tx_end_int_clr."]
    #[inline(always)]
    pub fn ch1_tx_end(&mut self) -> CH_TX_END_W<'_, INT_CLR_SPEC> {
        CH_TX_END_W::new(self, 1)
    }
    #[doc = "reg_ch(2-3)_rx_end_int_clr."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH2_RX_END` field.</div>"]
    #[inline(always)]
    pub fn ch_rx_end(&mut self, n: u8) -> CH_RX_END_W<'_, INT_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 2][n as usize];
        CH_RX_END_W::new(self, n + 2)
    }
    #[doc = "Bit 2 - reg_ch2_rx_end_int_clr."]
    #[inline(always)]
    pub fn ch2_rx_end(&mut self) -> CH_RX_END_W<'_, INT_CLR_SPEC> {
        CH_RX_END_W::new(self, 2)
    }
    #[doc = "Bit 3 - reg_ch3_rx_end_int_clr."]
    #[inline(always)]
    pub fn ch3_rx_end(&mut self) -> CH_RX_END_W<'_, INT_CLR_SPEC> {
        CH_RX_END_W::new(self, 3)
    }
    #[doc = "reg_ch(0-1)_err_int_clr."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH0_TX_ERR` field.</div>"]
    #[inline(always)]
    pub fn ch_tx_err(&mut self, n: u8) -> CH_TX_ERR_W<'_, INT_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 2][n as usize];
        CH_TX_ERR_W::new(self, n + 4)
    }
    #[doc = "Bit 4 - reg_ch0_err_int_clr."]
    #[inline(always)]
    pub fn ch0_tx_err(&mut self) -> CH_TX_ERR_W<'_, INT_CLR_SPEC> {
        CH_TX_ERR_W::new(self, 4)
    }
    #[doc = "Bit 5 - reg_ch1_err_int_clr."]
    #[inline(always)]
    pub fn ch1_tx_err(&mut self) -> CH_TX_ERR_W<'_, INT_CLR_SPEC> {
        CH_TX_ERR_W::new(self, 5)
    }
    #[doc = "reg_ch(2-3)_err_int_clr."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH2_RX_ERR` field.</div>"]
    #[inline(always)]
    pub fn ch_rx_err(&mut self, n: u8) -> CH_RX_ERR_W<'_, INT_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 2][n as usize];
        CH_RX_ERR_W::new(self, n + 6)
    }
    #[doc = "Bit 6 - reg_ch2_err_int_clr."]
    #[inline(always)]
    pub fn ch2_rx_err(&mut self) -> CH_RX_ERR_W<'_, INT_CLR_SPEC> {
        CH_RX_ERR_W::new(self, 6)
    }
    #[doc = "Bit 7 - reg_ch3_err_int_clr."]
    #[inline(always)]
    pub fn ch3_rx_err(&mut self) -> CH_RX_ERR_W<'_, INT_CLR_SPEC> {
        CH_RX_ERR_W::new(self, 7)
    }
    #[doc = "reg_ch(0-1)_tx_thr_event_int_clr."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH0_TX_THR_EVENT` field.</div>"]
    #[inline(always)]
    pub fn ch_tx_thr_event(&mut self, n: u8) -> CH_TX_THR_EVENT_W<'_, INT_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 2][n as usize];
        CH_TX_THR_EVENT_W::new(self, n + 8)
    }
    #[doc = "Bit 8 - reg_ch0_tx_thr_event_int_clr."]
    #[inline(always)]
    pub fn ch0_tx_thr_event(&mut self) -> CH_TX_THR_EVENT_W<'_, INT_CLR_SPEC> {
        CH_TX_THR_EVENT_W::new(self, 8)
    }
    #[doc = "Bit 9 - reg_ch1_tx_thr_event_int_clr."]
    #[inline(always)]
    pub fn ch1_tx_thr_event(&mut self) -> CH_TX_THR_EVENT_W<'_, INT_CLR_SPEC> {
        CH_TX_THR_EVENT_W::new(self, 9)
    }
    #[doc = "reg_ch(2-3)_rx_thr_event_int_clr."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH2_RX_THR_EVENT` field.</div>"]
    #[inline(always)]
    pub fn ch_rx_thr_event(&mut self, n: u8) -> CH_RX_THR_EVENT_W<'_, INT_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 2][n as usize];
        CH_RX_THR_EVENT_W::new(self, n + 10)
    }
    #[doc = "Bit 10 - reg_ch2_rx_thr_event_int_clr."]
    #[inline(always)]
    pub fn ch2_rx_thr_event(&mut self) -> CH_RX_THR_EVENT_W<'_, INT_CLR_SPEC> {
        CH_RX_THR_EVENT_W::new(self, 10)
    }
    #[doc = "Bit 11 - reg_ch3_rx_thr_event_int_clr."]
    #[inline(always)]
    pub fn ch3_rx_thr_event(&mut self) -> CH_RX_THR_EVENT_W<'_, INT_CLR_SPEC> {
        CH_RX_THR_EVENT_W::new(self, 11)
    }
    #[doc = "reg_ch(0-1)_tx_loop_int_clr."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH0_TX_LOOP` field.</div>"]
    #[inline(always)]
    pub fn ch_tx_loop(&mut self, n: u8) -> CH_TX_LOOP_W<'_, INT_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 2][n as usize];
        CH_TX_LOOP_W::new(self, n + 12)
    }
    #[doc = "Bit 12 - reg_ch0_tx_loop_int_clr."]
    #[inline(always)]
    pub fn ch0_tx_loop(&mut self) -> CH_TX_LOOP_W<'_, INT_CLR_SPEC> {
        CH_TX_LOOP_W::new(self, 12)
    }
    #[doc = "Bit 13 - reg_ch1_tx_loop_int_clr."]
    #[inline(always)]
    pub fn ch1_tx_loop(&mut self) -> CH_TX_LOOP_W<'_, INT_CLR_SPEC> {
        CH_TX_LOOP_W::new(self, 13)
    }
}
#[doc = "RMT_INT_CLR_REG.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_CLR_SPEC;
impl crate::RegisterSpec for INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`int_clr::W`](W) writer structure"]
impl crate::Writable for INT_CLR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_CLR to value 0"]
impl crate::Resettable for INT_CLR_SPEC {}
