#[doc = "Register `ALARMLO` reader"]
pub type R = crate::R<ALARMLO_SPEC>;
#[doc = "Register `ALARMLO` writer"]
pub type W = crate::W<ALARMLO_SPEC>;
#[doc = "Field `ALARM_LO` reader - reg_t0_alarm_lo."]
pub type ALARM_LO_R = crate::FieldReader<u32>;
#[doc = "Field `ALARM_LO` writer - reg_t0_alarm_lo."]
pub type ALARM_LO_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - reg_t0_alarm_lo."]
    #[inline(always)]
    pub fn alarm_lo(&self) -> ALARM_LO_R {
        ALARM_LO_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ALARMLO")
            .field("alarm_lo", &self.alarm_lo())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - reg_t0_alarm_lo."]
    #[inline(always)]
    pub fn alarm_lo(&mut self) -> ALARM_LO_W<'_, ALARMLO_SPEC> {
        ALARM_LO_W::new(self, 0)
    }
}
#[doc = "TIMG_T0ALARMLO_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`alarmlo::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`alarmlo::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ALARMLO_SPEC;
impl crate::RegisterSpec for ALARMLO_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`alarmlo::R`](R) reader structure"]
impl crate::Readable for ALARMLO_SPEC {}
#[doc = "`write(|w| ..)` method takes [`alarmlo::W`](W) writer structure"]
impl crate::Writable for ALARMLO_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ALARMLO to value 0"]
impl crate::Resettable for ALARMLO_SPEC {}
