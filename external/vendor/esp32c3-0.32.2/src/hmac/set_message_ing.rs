#[doc = "Register `SET_MESSAGE_ING` writer"]
pub type W = crate::W<SET_MESSAGE_ING_SPEC>;
#[doc = "Field `SET_TEXT_ING` writer - Continue typical hmac."]
pub type SET_TEXT_ING_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SET_MESSAGE_ING_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Continue typical hmac."]
    #[inline(always)]
    pub fn set_text_ing(&mut self) -> SET_TEXT_ING_W<'_, SET_MESSAGE_ING_SPEC> {
        SET_TEXT_ING_W::new(self, 0)
    }
}
#[doc = "Process control register 2.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`set_message_ing::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SET_MESSAGE_ING_SPEC;
impl crate::RegisterSpec for SET_MESSAGE_ING_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`set_message_ing::W`](W) writer structure"]
impl crate::Writable for SET_MESSAGE_ING_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SET_MESSAGE_ING to value 0"]
impl crate::Resettable for SET_MESSAGE_ING_SPEC {}
