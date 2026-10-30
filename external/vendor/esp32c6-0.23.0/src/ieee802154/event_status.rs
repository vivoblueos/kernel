#[doc = "Register `EVENT_STATUS` reader"]
pub type R = crate::R<EVENT_STATUS_SPEC>;
#[doc = "Register `EVENT_STATUS` writer"]
pub type W = crate::W<EVENT_STATUS_SPEC>;
#[doc = "Field `EVENT_STATUS` reader - "]
pub type EVENT_STATUS_R = crate::FieldReader<u16>;
#[doc = "Field `EVENT_STATUS` writer - "]
pub type EVENT_STATUS_W<'a, REG> = crate::FieldWriter<'a, REG, 13, u16>;
impl R {
    #[doc = "Bits 0:12"]
    #[inline(always)]
    pub fn event_status(&self) -> EVENT_STATUS_R {
        EVENT_STATUS_R::new((self.bits & 0x1fff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("EVENT_STATUS")
            .field("event_status", &self.event_status())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:12"]
    #[inline(always)]
    pub fn event_status(&mut self) -> EVENT_STATUS_W<'_, EVENT_STATUS_SPEC> {
        EVENT_STATUS_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`event_status::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`event_status::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct EVENT_STATUS_SPEC;
impl crate::RegisterSpec for EVENT_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`event_status::R`](R) reader structure"]
impl crate::Readable for EVENT_STATUS_SPEC {}
#[doc = "`write(|w| ..)` method takes [`event_status::W`](W) writer structure"]
impl crate::Writable for EVENT_STATUS_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets EVENT_STATUS to value 0"]
impl crate::Resettable for EVENT_STATUS_SPEC {}
