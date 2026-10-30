#[doc = "Register `ALARMHI` reader"]
pub type R = crate::R<ALARMHI_SPEC>;
#[doc = "Register `ALARMHI` writer"]
pub type W = crate::W<ALARMHI_SPEC>;
#[doc = "Field `ALARM_HI` reader - Timer %s alarm trigger time-base counter value, high 22 bits."]
pub type ALARM_HI_R = crate::FieldReader<u32>;
#[doc = "Field `ALARM_HI` writer - Timer %s alarm trigger time-base counter value, high 22 bits."]
pub type ALARM_HI_W<'a, REG> = crate::FieldWriter<'a, REG, 22, u32>;
impl R {
    #[doc = "Bits 0:21 - Timer %s alarm trigger time-base counter value, high 22 bits."]
    #[inline(always)]
    pub fn alarm_hi(&self) -> ALARM_HI_R {
        ALARM_HI_R::new(self.bits & 0x003f_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ALARMHI")
            .field("alarm_hi", &self.alarm_hi())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:21 - Timer %s alarm trigger time-base counter value, high 22 bits."]
    #[inline(always)]
    pub fn alarm_hi(&mut self) -> ALARM_HI_W<'_, ALARMHI_SPEC> {
        ALARM_HI_W::new(self, 0)
    }
}
#[doc = "Timer %s alarm value, high bits\n\nYou can [`read`](crate::Reg::read) this register and get [`alarmhi::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`alarmhi::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ALARMHI_SPEC;
impl crate::RegisterSpec for ALARMHI_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`alarmhi::R`](R) reader structure"]
impl crate::Readable for ALARMHI_SPEC {}
#[doc = "`write(|w| ..)` method takes [`alarmhi::W`](W) writer structure"]
impl crate::Writable for ALARMHI_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ALARMHI to value 0"]
impl crate::Resettable for ALARMHI_SPEC {}
