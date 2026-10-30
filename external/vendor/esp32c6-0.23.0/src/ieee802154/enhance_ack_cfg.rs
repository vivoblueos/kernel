#[doc = "Register `ENHANCE_ACK_CFG` reader"]
pub type R = crate::R<ENHANCE_ACK_CFG_SPEC>;
#[doc = "Register `ENHANCE_ACK_CFG` writer"]
pub type W = crate::W<ENHANCE_ACK_CFG_SPEC>;
#[doc = "Field `TX_ENH_ACK_GENERATE_DONE_NOTIFY` reader - "]
pub type TX_ENH_ACK_GENERATE_DONE_NOTIFY_R = crate::FieldReader<u32>;
#[doc = "Field `TX_ENH_ACK_GENERATE_DONE_NOTIFY` writer - "]
pub type TX_ENH_ACK_GENERATE_DONE_NOTIFY_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn tx_enh_ack_generate_done_notify(&self) -> TX_ENH_ACK_GENERATE_DONE_NOTIFY_R {
        TX_ENH_ACK_GENERATE_DONE_NOTIFY_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ENHANCE_ACK_CFG")
            .field(
                "tx_enh_ack_generate_done_notify",
                &self.tx_enh_ack_generate_done_notify(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn tx_enh_ack_generate_done_notify(
        &mut self,
    ) -> TX_ENH_ACK_GENERATE_DONE_NOTIFY_W<'_, ENHANCE_ACK_CFG_SPEC> {
        TX_ENH_ACK_GENERATE_DONE_NOTIFY_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`enhance_ack_cfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`enhance_ack_cfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ENHANCE_ACK_CFG_SPEC;
impl crate::RegisterSpec for ENHANCE_ACK_CFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`enhance_ack_cfg::R`](R) reader structure"]
impl crate::Readable for ENHANCE_ACK_CFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`enhance_ack_cfg::W`](W) writer structure"]
impl crate::Writable for ENHANCE_ACK_CFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ENHANCE_ACK_CFG to value 0"]
impl crate::Resettable for ENHANCE_ACK_CFG_SPEC {}
