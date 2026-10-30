#[doc = "Register `ACK_FRAME_PENDING_EN` reader"]
pub type R = crate::R<ACK_FRAME_PENDING_EN_SPEC>;
#[doc = "Register `ACK_FRAME_PENDING_EN` writer"]
pub type W = crate::W<ACK_FRAME_PENDING_EN_SPEC>;
#[doc = "Field `ACK_FRAME_PENDING_EN` reader - "]
pub type ACK_FRAME_PENDING_EN_R = crate::BitReader;
#[doc = "Field `ACK_FRAME_PENDING_EN` writer - "]
pub type ACK_FRAME_PENDING_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ACK_TX_ACK_TIMEOUT` reader - "]
pub type ACK_TX_ACK_TIMEOUT_R = crate::FieldReader<u16>;
#[doc = "Field `ACK_TX_ACK_TIMEOUT` writer - "]
pub type ACK_TX_ACK_TIMEOUT_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn ack_frame_pending_en(&self) -> ACK_FRAME_PENDING_EN_R {
        ACK_FRAME_PENDING_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 16:31"]
    #[inline(always)]
    pub fn ack_tx_ack_timeout(&self) -> ACK_TX_ACK_TIMEOUT_R {
        ACK_TX_ACK_TIMEOUT_R::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ACK_FRAME_PENDING_EN")
            .field("ack_frame_pending_en", &self.ack_frame_pending_en())
            .field("ack_tx_ack_timeout", &self.ack_tx_ack_timeout())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn ack_frame_pending_en(
        &mut self,
    ) -> ACK_FRAME_PENDING_EN_W<'_, ACK_FRAME_PENDING_EN_SPEC> {
        ACK_FRAME_PENDING_EN_W::new(self, 0)
    }
    #[doc = "Bits 16:31"]
    #[inline(always)]
    pub fn ack_tx_ack_timeout(&mut self) -> ACK_TX_ACK_TIMEOUT_W<'_, ACK_FRAME_PENDING_EN_SPEC> {
        ACK_TX_ACK_TIMEOUT_W::new(self, 16)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`ack_frame_pending_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ack_frame_pending_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ACK_FRAME_PENDING_EN_SPEC;
impl crate::RegisterSpec for ACK_FRAME_PENDING_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ack_frame_pending_en::R`](R) reader structure"]
impl crate::Readable for ACK_FRAME_PENDING_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ack_frame_pending_en::W`](W) writer structure"]
impl crate::Writable for ACK_FRAME_PENDING_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ACK_FRAME_PENDING_EN to value 0"]
impl crate::Resettable for ACK_FRAME_PENDING_EN_SPEC {}
