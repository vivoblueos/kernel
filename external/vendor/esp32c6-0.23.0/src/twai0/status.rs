#[doc = "Register `STATUS` reader"]
pub type R = crate::R<STATUS_SPEC>;
#[doc = "Field `RX_BUF_ST` reader - 1: full, one or more complete messages are available in the RXFIFO. 0: empty, no message is available"]
pub type RX_BUF_ST_R = crate::BitReader;
#[doc = "Field `OVERRUN` reader - 1: overrun, a message was lost because there was not enough space for that message in the RXFIFO. 0: absent, no data overrun has occurred since the last clear data overrun command was given"]
pub type OVERRUN_R = crate::BitReader;
#[doc = "Field `TX_BUF_ST` reader - 1: released, the CPU may write a message into the transmit buffer. 0: locked, the CPU cannot access the transmit buffer, a message is either waiting for transmission or is in the process of being transmitted"]
pub type TX_BUF_ST_R = crate::BitReader;
#[doc = "Field `TRANSMISSION_COMPLETE` reader - 1: complete, last requested transmission has been successfully completed. 0: incomplete, previously requested transmission is not yet completed"]
pub type TRANSMISSION_COMPLETE_R = crate::BitReader;
#[doc = "Field `RECEIVE` reader - 1: receive, the TWAI controller is receiving a message. 0: idle"]
pub type RECEIVE_R = crate::BitReader;
#[doc = "Field `TRANSMIT` reader - 1: transmit, the TWAI controller is transmitting a message. 0: idle"]
pub type TRANSMIT_R = crate::BitReader;
#[doc = "Field `ERR` reader - 1: error, at least one of the error counters has reached or exceeded the CPU warning limit defined by the Error Warning Limit Register (EWLR). 0: ok, both error counters are below the warning limit"]
pub type ERR_R = crate::BitReader;
#[doc = "Field `BUS_OFF_ST` reader - 1: bus-off, the TWAI controller is not involved in bus activities. 0: bus-on, the TWAI controller is involved in bus activities"]
pub type BUS_OFF_ST_R = crate::BitReader;
#[doc = "Field `MISS_ST` reader - 1: current message is destroyed because of FIFO overflow."]
pub type MISS_ST_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - 1: full, one or more complete messages are available in the RXFIFO. 0: empty, no message is available"]
    #[inline(always)]
    pub fn rx_buf_st(&self) -> RX_BUF_ST_R {
        RX_BUF_ST_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - 1: overrun, a message was lost because there was not enough space for that message in the RXFIFO. 0: absent, no data overrun has occurred since the last clear data overrun command was given"]
    #[inline(always)]
    pub fn overrun(&self) -> OVERRUN_R {
        OVERRUN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - 1: released, the CPU may write a message into the transmit buffer. 0: locked, the CPU cannot access the transmit buffer, a message is either waiting for transmission or is in the process of being transmitted"]
    #[inline(always)]
    pub fn tx_buf_st(&self) -> TX_BUF_ST_R {
        TX_BUF_ST_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - 1: complete, last requested transmission has been successfully completed. 0: incomplete, previously requested transmission is not yet completed"]
    #[inline(always)]
    pub fn transmission_complete(&self) -> TRANSMISSION_COMPLETE_R {
        TRANSMISSION_COMPLETE_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - 1: receive, the TWAI controller is receiving a message. 0: idle"]
    #[inline(always)]
    pub fn receive(&self) -> RECEIVE_R {
        RECEIVE_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - 1: transmit, the TWAI controller is transmitting a message. 0: idle"]
    #[inline(always)]
    pub fn transmit(&self) -> TRANSMIT_R {
        TRANSMIT_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - 1: error, at least one of the error counters has reached or exceeded the CPU warning limit defined by the Error Warning Limit Register (EWLR). 0: ok, both error counters are below the warning limit"]
    #[inline(always)]
    pub fn err(&self) -> ERR_R {
        ERR_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - 1: bus-off, the TWAI controller is not involved in bus activities. 0: bus-on, the TWAI controller is involved in bus activities"]
    #[inline(always)]
    pub fn bus_off_st(&self) -> BUS_OFF_ST_R {
        BUS_OFF_ST_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - 1: current message is destroyed because of FIFO overflow."]
    #[inline(always)]
    pub fn miss_st(&self) -> MISS_ST_R {
        MISS_ST_R::new(((self.bits >> 8) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("STATUS")
            .field("rx_buf_st", &self.rx_buf_st())
            .field("overrun", &self.overrun())
            .field("tx_buf_st", &self.tx_buf_st())
            .field("transmission_complete", &self.transmission_complete())
            .field("receive", &self.receive())
            .field("transmit", &self.transmit())
            .field("err", &self.err())
            .field("bus_off_st", &self.bus_off_st())
            .field("miss_st", &self.miss_st())
            .finish()
    }
}
#[doc = "TWAI status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`status::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct STATUS_SPEC;
impl crate::RegisterSpec for STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`status::R`](R) reader structure"]
impl crate::Readable for STATUS_SPEC {}
#[doc = "`reset()` method sets STATUS to value 0"]
impl crate::Resettable for STATUS_SPEC {}
