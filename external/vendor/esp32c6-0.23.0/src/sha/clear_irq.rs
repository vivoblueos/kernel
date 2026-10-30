#[doc = "Register `CLEAR_IRQ` writer"]
pub type W = crate::W<CLEAR_IRQ_SPEC>;
#[doc = "Field `CLEAR_INTERRUPT` writer - Clear sha interrupt."]
pub type CLEAR_INTERRUPT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<CLEAR_IRQ_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Clear sha interrupt."]
    #[inline(always)]
    pub fn clear_interrupt(&mut self) -> CLEAR_INTERRUPT_W<'_, CLEAR_IRQ_SPEC> {
        CLEAR_INTERRUPT_W::new(self, 0)
    }
}
#[doc = "Interrupt clear register.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clear_irq::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLEAR_IRQ_SPEC;
impl crate::RegisterSpec for CLEAR_IRQ_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`clear_irq::W`](W) writer structure"]
impl crate::Writable for CLEAR_IRQ_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLEAR_IRQ to value 0"]
impl crate::Resettable for CLEAR_IRQ_SPEC {}
