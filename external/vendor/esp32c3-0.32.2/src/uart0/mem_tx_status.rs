#[doc = "Register `MEM_TX_STATUS` reader"]
pub type R = crate::R<MEM_TX_STATUS_SPEC>;
#[doc = "Field `APB_TX_WADDR` reader - This register stores the offset address in Tx-FIFO when software writes Tx-FIFO via APB."]
pub type APB_TX_WADDR_R = crate::FieldReader<u16>;
#[doc = "Field `TX_RADDR` reader - This register stores the offset address in Tx-FIFO when Tx-FSM reads data via Tx-FIFO_Ctrl."]
pub type TX_RADDR_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:9 - This register stores the offset address in Tx-FIFO when software writes Tx-FIFO via APB."]
    #[inline(always)]
    pub fn apb_tx_waddr(&self) -> APB_TX_WADDR_R {
        APB_TX_WADDR_R::new((self.bits & 0x03ff) as u16)
    }
    #[doc = "Bits 11:20 - This register stores the offset address in Tx-FIFO when Tx-FSM reads data via Tx-FIFO_Ctrl."]
    #[inline(always)]
    pub fn tx_raddr(&self) -> TX_RADDR_R {
        TX_RADDR_R::new(((self.bits >> 11) & 0x03ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MEM_TX_STATUS")
            .field("apb_tx_waddr", &self.apb_tx_waddr())
            .field("tx_raddr", &self.tx_raddr())
            .finish()
    }
}
#[doc = "Tx-FIFO write and read offset address.\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_tx_status::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MEM_TX_STATUS_SPEC;
impl crate::RegisterSpec for MEM_TX_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mem_tx_status::R`](R) reader structure"]
impl crate::Readable for MEM_TX_STATUS_SPEC {}
#[doc = "`reset()` method sets MEM_TX_STATUS to value 0"]
impl crate::Resettable for MEM_TX_STATUS_SPEC {}
