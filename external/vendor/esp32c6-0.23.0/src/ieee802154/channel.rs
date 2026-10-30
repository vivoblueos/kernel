#[doc = "Register `CHANNEL` reader"]
pub type R = crate::R<CHANNEL_SPEC>;
#[doc = "Register `CHANNEL` writer"]
pub type W = crate::W<CHANNEL_SPEC>;
#[doc = "Field `HOP` reader - "]
pub type HOP_R = crate::FieldReader;
#[doc = "Field `HOP` writer - "]
pub type HOP_W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
impl R {
    #[doc = "Bits 0:6"]
    #[inline(always)]
    pub fn hop(&self) -> HOP_R {
        HOP_R::new((self.bits & 0x7f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CHANNEL").field("hop", &self.hop()).finish()
    }
}
impl W {
    #[doc = "Bits 0:6"]
    #[inline(always)]
    pub fn hop(&mut self) -> HOP_W<'_, CHANNEL_SPEC> {
        HOP_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`channel::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`channel::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CHANNEL_SPEC;
impl crate::RegisterSpec for CHANNEL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`channel::R`](R) reader structure"]
impl crate::Readable for CHANNEL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`channel::W`](W) writer structure"]
impl crate::Writable for CHANNEL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CHANNEL to value 0"]
impl crate::Resettable for CHANNEL_SPEC {}
