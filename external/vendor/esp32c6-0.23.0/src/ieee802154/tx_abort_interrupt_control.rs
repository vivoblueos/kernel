#[doc = "Register `TX_ABORT_INTERRUPT_CONTROL` reader"]
pub type R = crate::R<TX_ABORT_INTERRUPT_CONTROL_SPEC>;
#[doc = "Register `TX_ABORT_INTERRUPT_CONTROL` writer"]
pub type W = crate::W<TX_ABORT_INTERRUPT_CONTROL_SPEC>;
#[doc = "Field `TX_ABORT_INTERRUPT_CONTROL` reader - "]
pub type TX_ABORT_INTERRUPT_CONTROL_R = crate::FieldReader<u32>;
#[doc = "Field `TX_ABORT_INTERRUPT_CONTROL` writer - "]
pub type TX_ABORT_INTERRUPT_CONTROL_W<'a, REG> = crate::FieldWriter<'a, REG, 31, u32>;
impl R {
    #[doc = "Bits 0:30"]
    #[inline(always)]
    pub fn tx_abort_interrupt_control(&self) -> TX_ABORT_INTERRUPT_CONTROL_R {
        TX_ABORT_INTERRUPT_CONTROL_R::new(self.bits & 0x7fff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_ABORT_INTERRUPT_CONTROL")
            .field(
                "tx_abort_interrupt_control",
                &self.tx_abort_interrupt_control(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:30"]
    #[inline(always)]
    pub fn tx_abort_interrupt_control(
        &mut self,
    ) -> TX_ABORT_INTERRUPT_CONTROL_W<'_, TX_ABORT_INTERRUPT_CONTROL_SPEC> {
        TX_ABORT_INTERRUPT_CONTROL_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_abort_interrupt_control::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_abort_interrupt_control::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_ABORT_INTERRUPT_CONTROL_SPEC;
impl crate::RegisterSpec for TX_ABORT_INTERRUPT_CONTROL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_abort_interrupt_control::R`](R) reader structure"]
impl crate::Readable for TX_ABORT_INTERRUPT_CONTROL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_abort_interrupt_control::W`](W) writer structure"]
impl crate::Writable for TX_ABORT_INTERRUPT_CONTROL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_ABORT_INTERRUPT_CONTROL to value 0"]
impl crate::Resettable for TX_ABORT_INTERRUPT_CONTROL_SPEC {}
