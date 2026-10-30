#[doc = "Register `INT_ST` reader"]
pub type R = crate::R<INT_ST_SPEC>;
#[doc = "Field `RX_DONE` reader - The masked interrupt status bit for the i2s_rx_done_int interrupt"]
pub type RX_DONE_R = crate::BitReader;
#[doc = "Field `TX_DONE` reader - The masked interrupt status bit for the i2s_tx_done_int interrupt"]
pub type TX_DONE_R = crate::BitReader;
#[doc = "Field `RX_HUNG` reader - The masked interrupt status bit for the i2s_rx_hung_int interrupt"]
pub type RX_HUNG_R = crate::BitReader;
#[doc = "Field `TX_HUNG` reader - The masked interrupt status bit for the i2s_tx_hung_int interrupt"]
pub type TX_HUNG_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The masked interrupt status bit for the i2s_rx_done_int interrupt"]
    #[inline(always)]
    pub fn rx_done(&self) -> RX_DONE_R {
        RX_DONE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The masked interrupt status bit for the i2s_tx_done_int interrupt"]
    #[inline(always)]
    pub fn tx_done(&self) -> TX_DONE_R {
        TX_DONE_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The masked interrupt status bit for the i2s_rx_hung_int interrupt"]
    #[inline(always)]
    pub fn rx_hung(&self) -> RX_HUNG_R {
        RX_HUNG_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The masked interrupt status bit for the i2s_tx_hung_int interrupt"]
    #[inline(always)]
    pub fn tx_hung(&self) -> TX_HUNG_R {
        TX_HUNG_R::new(((self.bits >> 3) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_ST")
            .field("rx_done", &self.rx_done())
            .field("tx_done", &self.tx_done())
            .field("rx_hung", &self.rx_hung())
            .field("tx_hung", &self.tx_hung())
            .finish()
    }
}
#[doc = "I2S interrupt status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_ST_SPEC;
impl crate::RegisterSpec for INT_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_st::R`](R) reader structure"]
impl crate::Readable for INT_ST_SPEC {}
#[doc = "`reset()` method sets INT_ST to value 0"]
impl crate::Resettable for INT_ST_SPEC {}
