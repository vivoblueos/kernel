#[doc = "Register `CAP_TIMER_PHASE` reader"]
pub type R = crate::R<CAP_TIMER_PHASE_SPEC>;
#[doc = "Register `CAP_TIMER_PHASE` writer"]
pub type W = crate::W<CAP_TIMER_PHASE_SPEC>;
#[doc = "Field `CAP_PHASE` reader - Phase value for capture timer sync operation."]
pub type CAP_PHASE_R = crate::FieldReader<u32>;
#[doc = "Field `CAP_PHASE` writer - Phase value for capture timer sync operation."]
pub type CAP_PHASE_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Phase value for capture timer sync operation."]
    #[inline(always)]
    pub fn cap_phase(&self) -> CAP_PHASE_R {
        CAP_PHASE_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CAP_TIMER_PHASE")
            .field("cap_phase", &self.cap_phase())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Phase value for capture timer sync operation."]
    #[inline(always)]
    pub fn cap_phase(&mut self) -> CAP_PHASE_W<'_, CAP_TIMER_PHASE_SPEC> {
        CAP_PHASE_W::new(self, 0)
    }
}
#[doc = "Phase for capture timer sync\n\nYou can [`read`](crate::Reg::read) this register and get [`cap_timer_phase::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cap_timer_phase::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CAP_TIMER_PHASE_SPEC;
impl crate::RegisterSpec for CAP_TIMER_PHASE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cap_timer_phase::R`](R) reader structure"]
impl crate::Readable for CAP_TIMER_PHASE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cap_timer_phase::W`](W) writer structure"]
impl crate::Writable for CAP_TIMER_PHASE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CAP_TIMER_PHASE to value 0"]
impl crate::Resettable for CAP_TIMER_PHASE_SPEC {}
