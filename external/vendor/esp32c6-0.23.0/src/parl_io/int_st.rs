#[doc = "Register `INT_ST` reader"]
pub type R = crate::R<INT_ST_SPEC>;
#[doc = "Field `TX_FIFO_REMPTY` reader - The masked interrupt status of TX_FIFO_REMPTY_INTR."]
pub type TX_FIFO_REMPTY_R = crate::BitReader;
#[doc = "Field `RX_FIFO_WOVF` reader - The masked interrupt status of RX_FIFO_WOVF_INTR."]
pub type RX_FIFO_WOVF_R = crate::BitReader;
#[doc = "Field `TX_EOF` reader - The masked interrupt status of TX_EOF_INTR."]
pub type TX_EOF_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The masked interrupt status of TX_FIFO_REMPTY_INTR."]
    #[inline(always)]
    pub fn tx_fifo_rempty(&self) -> TX_FIFO_REMPTY_R {
        TX_FIFO_REMPTY_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The masked interrupt status of RX_FIFO_WOVF_INTR."]
    #[inline(always)]
    pub fn rx_fifo_wovf(&self) -> RX_FIFO_WOVF_R {
        RX_FIFO_WOVF_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The masked interrupt status of TX_EOF_INTR."]
    #[inline(always)]
    pub fn tx_eof(&self) -> TX_EOF_R {
        TX_EOF_R::new(((self.bits >> 2) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_ST")
            .field("tx_fifo_rempty", &self.tx_fifo_rempty())
            .field("rx_fifo_wovf", &self.rx_fifo_wovf())
            .field("tx_eof", &self.tx_eof())
            .finish()
    }
}
#[doc = "Parallel IO interrupt singal status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_ST_SPEC;
impl crate::RegisterSpec for INT_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_st::R`](R) reader structure"]
impl crate::Readable for INT_ST_SPEC {}
#[doc = "`reset()` method sets INT_ST to value 0"]
impl crate::Resettable for INT_ST_SPEC {}
