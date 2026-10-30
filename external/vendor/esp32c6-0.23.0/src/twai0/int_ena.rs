#[doc = "Register `INT_ENA` reader"]
pub type R = crate::R<INT_ENA_SPEC>;
#[doc = "Register `INT_ENA` writer"]
pub type W = crate::W<INT_ENA_SPEC>;
#[doc = "Field `RX_INT_ENA` reader - 1: enabled, when the receive buffer status is 'full' the TWAI controller requests the respective interrupt. 0: disable"]
pub type RX_INT_ENA_R = crate::BitReader;
#[doc = "Field `RX_INT_ENA` writer - 1: enabled, when the receive buffer status is 'full' the TWAI controller requests the respective interrupt. 0: disable"]
pub type RX_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_INT_ENA` reader - 1: enabled, when a message has been successfully transmitted or the transmit buffer is accessible again (e.g. after an abort transmission command), the TWAI controller requests the respective interrupt. 0: disable"]
pub type TX_INT_ENA_R = crate::BitReader;
#[doc = "Field `TX_INT_ENA` writer - 1: enabled, when a message has been successfully transmitted or the transmit buffer is accessible again (e.g. after an abort transmission command), the TWAI controller requests the respective interrupt. 0: disable"]
pub type TX_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXT_ERR_WARNING_INT_ENA` reader - 1: enabled, if the error or bus status change (see status register. Table 14), the TWAI controllerrequests the respective interrupt. 0: disable"]
pub type EXT_ERR_WARNING_INT_ENA_R = crate::BitReader;
#[doc = "Field `EXT_ERR_WARNING_INT_ENA` writer - 1: enabled, if the error or bus status change (see status register. Table 14), the TWAI controllerrequests the respective interrupt. 0: disable"]
pub type EXT_ERR_WARNING_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXT_DATA_OVERRUN_INT_ENA` reader - 1: enabled, if the data overrun status bit is set (see status register. Table 14), the TWAI controllerrequests the respective interrupt. 0: disable"]
pub type EXT_DATA_OVERRUN_INT_ENA_R = crate::BitReader;
#[doc = "Field `EXT_DATA_OVERRUN_INT_ENA` writer - 1: enabled, if the data overrun status bit is set (see status register. Table 14), the TWAI controllerrequests the respective interrupt. 0: disable"]
pub type EXT_DATA_OVERRUN_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ERR_PASSIVE_INT_ENA` reader - 1: enabled, if the error status of the TWAI controller changes from error active to error passive or vice versa, the respective interrupt is requested. 0: disable"]
pub type ERR_PASSIVE_INT_ENA_R = crate::BitReader;
#[doc = "Field `ERR_PASSIVE_INT_ENA` writer - 1: enabled, if the error status of the TWAI controller changes from error active to error passive or vice versa, the respective interrupt is requested. 0: disable"]
pub type ERR_PASSIVE_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ARB_LOST_INT_ENA` reader - 1: enabled, if the TWAI controller has lost arbitration, the respective interrupt is requested. 0: disable"]
pub type ARB_LOST_INT_ENA_R = crate::BitReader;
#[doc = "Field `ARB_LOST_INT_ENA` writer - 1: enabled, if the TWAI controller has lost arbitration, the respective interrupt is requested. 0: disable"]
pub type ARB_LOST_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BUS_ERR_INT_ENA` reader - 1: enabled, if an bus error has been detected, the TWAI controller requests the respective interrupt. 0: disable"]
pub type BUS_ERR_INT_ENA_R = crate::BitReader;
#[doc = "Field `BUS_ERR_INT_ENA` writer - 1: enabled, if an bus error has been detected, the TWAI controller requests the respective interrupt. 0: disable"]
pub type BUS_ERR_INT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IDLE_INT_ENA` reader - 1: enabled, if state of TWAI become IDLE, the TWAI controller requests the respective interrupt. 0: disable"]
pub type IDLE_INT_ENA_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - 1: enabled, when the receive buffer status is 'full' the TWAI controller requests the respective interrupt. 0: disable"]
    #[inline(always)]
    pub fn rx_int_ena(&self) -> RX_INT_ENA_R {
        RX_INT_ENA_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - 1: enabled, when a message has been successfully transmitted or the transmit buffer is accessible again (e.g. after an abort transmission command), the TWAI controller requests the respective interrupt. 0: disable"]
    #[inline(always)]
    pub fn tx_int_ena(&self) -> TX_INT_ENA_R {
        TX_INT_ENA_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - 1: enabled, if the error or bus status change (see status register. Table 14), the TWAI controllerrequests the respective interrupt. 0: disable"]
    #[inline(always)]
    pub fn ext_err_warning_int_ena(&self) -> EXT_ERR_WARNING_INT_ENA_R {
        EXT_ERR_WARNING_INT_ENA_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - 1: enabled, if the data overrun status bit is set (see status register. Table 14), the TWAI controllerrequests the respective interrupt. 0: disable"]
    #[inline(always)]
    pub fn ext_data_overrun_int_ena(&self) -> EXT_DATA_OVERRUN_INT_ENA_R {
        EXT_DATA_OVERRUN_INT_ENA_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 5 - 1: enabled, if the error status of the TWAI controller changes from error active to error passive or vice versa, the respective interrupt is requested. 0: disable"]
    #[inline(always)]
    pub fn err_passive_int_ena(&self) -> ERR_PASSIVE_INT_ENA_R {
        ERR_PASSIVE_INT_ENA_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - 1: enabled, if the TWAI controller has lost arbitration, the respective interrupt is requested. 0: disable"]
    #[inline(always)]
    pub fn arb_lost_int_ena(&self) -> ARB_LOST_INT_ENA_R {
        ARB_LOST_INT_ENA_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - 1: enabled, if an bus error has been detected, the TWAI controller requests the respective interrupt. 0: disable"]
    #[inline(always)]
    pub fn bus_err_int_ena(&self) -> BUS_ERR_INT_ENA_R {
        BUS_ERR_INT_ENA_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - 1: enabled, if state of TWAI become IDLE, the TWAI controller requests the respective interrupt. 0: disable"]
    #[inline(always)]
    pub fn idle_int_ena(&self) -> IDLE_INT_ENA_R {
        IDLE_INT_ENA_R::new(((self.bits >> 8) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_ENA")
            .field("rx_int_ena", &self.rx_int_ena())
            .field("tx_int_ena", &self.tx_int_ena())
            .field("ext_err_warning_int_ena", &self.ext_err_warning_int_ena())
            .field("ext_data_overrun_int_ena", &self.ext_data_overrun_int_ena())
            .field("err_passive_int_ena", &self.err_passive_int_ena())
            .field("arb_lost_int_ena", &self.arb_lost_int_ena())
            .field("bus_err_int_ena", &self.bus_err_int_ena())
            .field("idle_int_ena", &self.idle_int_ena())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - 1: enabled, when the receive buffer status is 'full' the TWAI controller requests the respective interrupt. 0: disable"]
    #[inline(always)]
    pub fn rx_int_ena(&mut self) -> RX_INT_ENA_W<'_, INT_ENA_SPEC> {
        RX_INT_ENA_W::new(self, 0)
    }
    #[doc = "Bit 1 - 1: enabled, when a message has been successfully transmitted or the transmit buffer is accessible again (e.g. after an abort transmission command), the TWAI controller requests the respective interrupt. 0: disable"]
    #[inline(always)]
    pub fn tx_int_ena(&mut self) -> TX_INT_ENA_W<'_, INT_ENA_SPEC> {
        TX_INT_ENA_W::new(self, 1)
    }
    #[doc = "Bit 2 - 1: enabled, if the error or bus status change (see status register. Table 14), the TWAI controllerrequests the respective interrupt. 0: disable"]
    #[inline(always)]
    pub fn ext_err_warning_int_ena(&mut self) -> EXT_ERR_WARNING_INT_ENA_W<'_, INT_ENA_SPEC> {
        EXT_ERR_WARNING_INT_ENA_W::new(self, 2)
    }
    #[doc = "Bit 3 - 1: enabled, if the data overrun status bit is set (see status register. Table 14), the TWAI controllerrequests the respective interrupt. 0: disable"]
    #[inline(always)]
    pub fn ext_data_overrun_int_ena(&mut self) -> EXT_DATA_OVERRUN_INT_ENA_W<'_, INT_ENA_SPEC> {
        EXT_DATA_OVERRUN_INT_ENA_W::new(self, 3)
    }
    #[doc = "Bit 5 - 1: enabled, if the error status of the TWAI controller changes from error active to error passive or vice versa, the respective interrupt is requested. 0: disable"]
    #[inline(always)]
    pub fn err_passive_int_ena(&mut self) -> ERR_PASSIVE_INT_ENA_W<'_, INT_ENA_SPEC> {
        ERR_PASSIVE_INT_ENA_W::new(self, 5)
    }
    #[doc = "Bit 6 - 1: enabled, if the TWAI controller has lost arbitration, the respective interrupt is requested. 0: disable"]
    #[inline(always)]
    pub fn arb_lost_int_ena(&mut self) -> ARB_LOST_INT_ENA_W<'_, INT_ENA_SPEC> {
        ARB_LOST_INT_ENA_W::new(self, 6)
    }
    #[doc = "Bit 7 - 1: enabled, if an bus error has been detected, the TWAI controller requests the respective interrupt. 0: disable"]
    #[inline(always)]
    pub fn bus_err_int_ena(&mut self) -> BUS_ERR_INT_ENA_W<'_, INT_ENA_SPEC> {
        BUS_ERR_INT_ENA_W::new(self, 7)
    }
}
#[doc = "Interrupt enable register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
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
