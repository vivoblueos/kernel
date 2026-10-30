#[doc = "Register `CMD` writer"]
pub type W = crate::W<CMD_SPEC>;
#[doc = "Field `TX_REQ` writer - 1: present, a message shall be transmitted. 0: absent"]
pub type TX_REQ_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ABORT_TX` writer - 1: present, if not already in progress, a pending transmission request is cancelled. 0: absent"]
pub type ABORT_TX_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RELEASE_BUF` writer - 1: released, the receive buffer, representing the message memory space in the RXFIFO is released. 0: no action"]
pub type RELEASE_BUF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLEAR_DATA_OVERRUN` writer - 1: clear, the data overrun status bit is cleared. 0: no action."]
pub type CLEAR_DATA_OVERRUN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SELF_RX_REQ` writer - 1: present, a message shall be transmitted and received simultaneously. 0: absent."]
pub type SELF_RX_REQ_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<CMD_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - 1: present, a message shall be transmitted. 0: absent"]
    #[inline(always)]
    pub fn tx_req(&mut self) -> TX_REQ_W<'_, CMD_SPEC> {
        TX_REQ_W::new(self, 0)
    }
    #[doc = "Bit 1 - 1: present, if not already in progress, a pending transmission request is cancelled. 0: absent"]
    #[inline(always)]
    pub fn abort_tx(&mut self) -> ABORT_TX_W<'_, CMD_SPEC> {
        ABORT_TX_W::new(self, 1)
    }
    #[doc = "Bit 2 - 1: released, the receive buffer, representing the message memory space in the RXFIFO is released. 0: no action"]
    #[inline(always)]
    pub fn release_buf(&mut self) -> RELEASE_BUF_W<'_, CMD_SPEC> {
        RELEASE_BUF_W::new(self, 2)
    }
    #[doc = "Bit 3 - 1: clear, the data overrun status bit is cleared. 0: no action."]
    #[inline(always)]
    pub fn clear_data_overrun(&mut self) -> CLEAR_DATA_OVERRUN_W<'_, CMD_SPEC> {
        CLEAR_DATA_OVERRUN_W::new(self, 3)
    }
    #[doc = "Bit 4 - 1: present, a message shall be transmitted and received simultaneously. 0: absent."]
    #[inline(always)]
    pub fn self_rx_req(&mut self) -> SELF_RX_REQ_W<'_, CMD_SPEC> {
        SELF_RX_REQ_W::new(self, 4)
    }
}
#[doc = "TWAI command register.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cmd::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CMD_SPEC;
impl crate::RegisterSpec for CMD_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`cmd::W`](W) writer structure"]
impl crate::Writable for CMD_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CMD to value 0"]
impl crate::Resettable for CMD_SPEC {}
