#[doc = "Register `EVENT_EN` reader"]
pub type R = crate::R<EVENT_EN_SPEC>;
#[doc = "Register `EVENT_EN` writer"]
pub type W = crate::W<EVENT_EN_SPEC>;
#[doc = "Field `EVENT_EN` reader - "]
pub type EVENT_EN_R = crate::FieldReader<u16>;
#[doc = "Field `EVENT_EN` writer - "]
pub type EVENT_EN_W<'a, REG> = crate::FieldWriter<'a, REG, 13, u16>;
impl R {
    #[doc = "Bits 0:12"]
    #[inline(always)]
    pub fn event_en(&self) -> EVENT_EN_R {
        EVENT_EN_R::new((self.bits & 0x1fff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("EVENT_EN")
            .field("event_en", &self.event_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:12"]
    #[inline(always)]
    pub fn event_en(&mut self) -> EVENT_EN_W<'_, EVENT_EN_SPEC> {
        EVENT_EN_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`event_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`event_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct EVENT_EN_SPEC;
impl crate::RegisterSpec for EVENT_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`event_en::R`](R) reader structure"]
impl crate::Readable for EVENT_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`event_en::W`](W) writer structure"]
impl crate::Writable for EVENT_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets EVENT_EN to value 0"]
impl crate::Resettable for EVENT_EN_SPEC {}
