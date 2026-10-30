#[doc = "Register `STATE` reader"]
pub type R = crate::R<STATE_SPEC>;
#[doc = "Field `TX_IDLE` reader - 1: i2s_tx is idle state. 0: i2s_tx is working."]
pub type TX_IDLE_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - 1: i2s_tx is idle state. 0: i2s_tx is working."]
    #[inline(always)]
    pub fn tx_idle(&self) -> TX_IDLE_R {
        TX_IDLE_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("STATE")
            .field("tx_idle", &self.tx_idle())
            .finish()
    }
}
#[doc = "I2S TX status register\n\nYou can [`read`](crate::Reg::read) this register and get [`state::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct STATE_SPEC;
impl crate::RegisterSpec for STATE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`state::R`](R) reader structure"]
impl crate::Readable for STATE_SPEC {}
#[doc = "`reset()` method sets STATE to value 0x01"]
impl crate::Resettable for STATE_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
