#[doc = "Register `IRQ_ENA` reader"]
pub type R = crate::R<IRQ_ENA_SPEC>;
#[doc = "Register `IRQ_ENA` writer"]
pub type W = crate::W<IRQ_ENA_SPEC>;
#[doc = "Field `INTERRUPT_ENA` reader - Sha interrupt enable register. 1'b0: disable(default). 1'b1: enable."]
pub type INTERRUPT_ENA_R = crate::BitReader;
#[doc = "Field `INTERRUPT_ENA` writer - Sha interrupt enable register. 1'b0: disable(default). 1'b1: enable."]
pub type INTERRUPT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Sha interrupt enable register. 1'b0: disable(default). 1'b1: enable."]
    #[inline(always)]
    pub fn interrupt_ena(&self) -> INTERRUPT_ENA_R {
        INTERRUPT_ENA_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IRQ_ENA")
            .field("interrupt_ena", &self.interrupt_ena())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Sha interrupt enable register. 1'b0: disable(default). 1'b1: enable."]
    #[inline(always)]
    pub fn interrupt_ena(&mut self) -> INTERRUPT_ENA_W<'_, IRQ_ENA_SPEC> {
        INTERRUPT_ENA_W::new(self, 0)
    }
}
#[doc = "Interrupt enable register.\n\nYou can [`read`](crate::Reg::read) this register and get [`irq_ena::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`irq_ena::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IRQ_ENA_SPEC;
impl crate::RegisterSpec for IRQ_ENA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`irq_ena::R`](R) reader structure"]
impl crate::Readable for IRQ_ENA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`irq_ena::W`](W) writer structure"]
impl crate::Writable for IRQ_ENA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IRQ_ENA to value 0"]
impl crate::Resettable for IRQ_ENA_SPEC {}
