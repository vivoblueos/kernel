#[doc = "Register `SET_MESSAGE_ONE` writer"]
pub type W = crate::W<SET_MESSAGE_ONE_SPEC>;
#[doc = "Field `SET_TEXT_ONE` writer - Call SHA to calculate one message block."]
pub type SET_TEXT_ONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SET_MESSAGE_ONE_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Call SHA to calculate one message block."]
    #[inline(always)]
    pub fn set_text_one(&mut self) -> SET_TEXT_ONE_W<'_, SET_MESSAGE_ONE_SPEC> {
        SET_TEXT_ONE_W::new(self, 0)
    }
}
#[doc = "Process control register 1.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`set_message_one::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SET_MESSAGE_ONE_SPEC;
impl crate::RegisterSpec for SET_MESSAGE_ONE_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`set_message_one::W`](W) writer structure"]
impl crate::Writable for SET_MESSAGE_ONE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SET_MESSAGE_ONE to value 0"]
impl crate::Resettable for SET_MESSAGE_ONE_SPEC {}
