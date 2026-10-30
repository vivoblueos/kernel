#[doc = "Register `TX_ACK_ABORT_COEX_CNT` reader"]
pub type R = crate::R<TX_ACK_ABORT_COEX_CNT_SPEC>;
#[doc = "Register `TX_ACK_ABORT_COEX_CNT` writer"]
pub type W = crate::W<TX_ACK_ABORT_COEX_CNT_SPEC>;
#[doc = "Field `TX_ACK_ABORT_COEX_CNT` reader - "]
pub type TX_ACK_ABORT_COEX_CNT_R = crate::FieldReader<u16>;
#[doc = "Field `TX_ACK_ABORT_COEX_CNT` writer - "]
pub type TX_ACK_ABORT_COEX_CNT_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn tx_ack_abort_coex_cnt(&self) -> TX_ACK_ABORT_COEX_CNT_R {
        TX_ACK_ABORT_COEX_CNT_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_ACK_ABORT_COEX_CNT")
            .field("tx_ack_abort_coex_cnt", &self.tx_ack_abort_coex_cnt())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn tx_ack_abort_coex_cnt(
        &mut self,
    ) -> TX_ACK_ABORT_COEX_CNT_W<'_, TX_ACK_ABORT_COEX_CNT_SPEC> {
        TX_ACK_ABORT_COEX_CNT_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_ack_abort_coex_cnt::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_ack_abort_coex_cnt::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_ACK_ABORT_COEX_CNT_SPEC;
impl crate::RegisterSpec for TX_ACK_ABORT_COEX_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_ack_abort_coex_cnt::R`](R) reader structure"]
impl crate::Readable for TX_ACK_ABORT_COEX_CNT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_ack_abort_coex_cnt::W`](W) writer structure"]
impl crate::Writable for TX_ACK_ABORT_COEX_CNT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_ACK_ABORT_COEX_CNT to value 0"]
impl crate::Resettable for TX_ACK_ABORT_COEX_CNT_SPEC {}
