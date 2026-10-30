#[doc = "Register `INT_RAW` reader"]
pub type R = crate::R<INT_RAW_SPEC>;
#[doc = "Field `RX_INT_ST` reader - Receive interrupt. If this bit is set to 1, it indicates there are messages to be handled in the RX FIFO."]
pub type RX_INT_ST_R = crate::BitReader;
#[doc = "Field `TX_INT_ST` reader - Transmit interrupt. If this bit is set to 1, it indicates the message transmitting mis- sion is finished and a new transmission is able to execute."]
pub type TX_INT_ST_R = crate::BitReader;
#[doc = "Field `ERR_WARN_INT_ST` reader - Error warning interrupt. If this bit is set to 1, it indicates the error status signal and the bus-off status signal of Status register have changed (e.g., switched from 0 to 1 or from 1 to 0)."]
pub type ERR_WARN_INT_ST_R = crate::BitReader;
#[doc = "Field `OVERRUN_INT_ST` reader - Data overrun interrupt. If this bit is set to 1, it indicates a data overrun interrupt is generated in the RX FIFO."]
pub type OVERRUN_INT_ST_R = crate::BitReader;
#[doc = "Field `ERR_PASSIVE_INT_ST` reader - Error passive interrupt. If this bit is set to 1, it indicates the TWAI Controller is switched between error active status and error passive status due to the change of error counters."]
pub type ERR_PASSIVE_INT_ST_R = crate::BitReader;
#[doc = "Field `ARB_LOST_INT_ST` reader - Arbitration lost interrupt. If this bit is set to 1, it indicates an arbitration lost interrupt is generated."]
pub type ARB_LOST_INT_ST_R = crate::BitReader;
#[doc = "Field `BUS_ERR_INT_ST` reader - Error interrupt. If this bit is set to 1, it indicates an error is detected on the bus."]
pub type BUS_ERR_INT_ST_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Receive interrupt. If this bit is set to 1, it indicates there are messages to be handled in the RX FIFO."]
    #[inline(always)]
    pub fn rx_int_st(&self) -> RX_INT_ST_R {
        RX_INT_ST_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Transmit interrupt. If this bit is set to 1, it indicates the message transmitting mis- sion is finished and a new transmission is able to execute."]
    #[inline(always)]
    pub fn tx_int_st(&self) -> TX_INT_ST_R {
        TX_INT_ST_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Error warning interrupt. If this bit is set to 1, it indicates the error status signal and the bus-off status signal of Status register have changed (e.g., switched from 0 to 1 or from 1 to 0)."]
    #[inline(always)]
    pub fn err_warn_int_st(&self) -> ERR_WARN_INT_ST_R {
        ERR_WARN_INT_ST_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Data overrun interrupt. If this bit is set to 1, it indicates a data overrun interrupt is generated in the RX FIFO."]
    #[inline(always)]
    pub fn overrun_int_st(&self) -> OVERRUN_INT_ST_R {
        OVERRUN_INT_ST_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 5 - Error passive interrupt. If this bit is set to 1, it indicates the TWAI Controller is switched between error active status and error passive status due to the change of error counters."]
    #[inline(always)]
    pub fn err_passive_int_st(&self) -> ERR_PASSIVE_INT_ST_R {
        ERR_PASSIVE_INT_ST_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Arbitration lost interrupt. If this bit is set to 1, it indicates an arbitration lost interrupt is generated."]
    #[inline(always)]
    pub fn arb_lost_int_st(&self) -> ARB_LOST_INT_ST_R {
        ARB_LOST_INT_ST_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Error interrupt. If this bit is set to 1, it indicates an error is detected on the bus."]
    #[inline(always)]
    pub fn bus_err_int_st(&self) -> BUS_ERR_INT_ST_R {
        BUS_ERR_INT_ST_R::new(((self.bits >> 7) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_RAW")
            .field("rx_int_st", &self.rx_int_st())
            .field("tx_int_st", &self.tx_int_st())
            .field("err_warn_int_st", &self.err_warn_int_st())
            .field("overrun_int_st", &self.overrun_int_st())
            .field("err_passive_int_st", &self.err_passive_int_st())
            .field("arb_lost_int_st", &self.arb_lost_int_st())
            .field("bus_err_int_st", &self.bus_err_int_st())
            .finish()
    }
}
#[doc = "Interrupt Register\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_RAW_SPEC;
impl crate::RegisterSpec for INT_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_raw::R`](R) reader structure"]
impl crate::Readable for INT_RAW_SPEC {}
#[doc = "`reset()` method sets INT_RAW to value 0"]
impl crate::Resettable for INT_RAW_SPEC {}
