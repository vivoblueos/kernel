#[doc = "Register `SET_RESULT_FINISH` writer"]
pub type W = crate::W<SET_RESULT_FINISH_SPEC>;
#[doc = "Field `SET_RESULT_END` writer - After read result from upstream, then let hmac back to idle."]
pub type SET_RESULT_END_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SET_RESULT_FINISH_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - After read result from upstream, then let hmac back to idle."]
    #[inline(always)]
    pub fn set_result_end(&mut self) -> SET_RESULT_END_W<'_, SET_RESULT_FINISH_SPEC> {
        SET_RESULT_END_W::new(self, 0)
    }
}
#[doc = "Process control register 4.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`set_result_finish::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SET_RESULT_FINISH_SPEC;
impl crate::RegisterSpec for SET_RESULT_FINISH_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`set_result_finish::W`](W) writer structure"]
impl crate::Writable for SET_RESULT_FINISH_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SET_RESULT_FINISH to value 0"]
impl crate::Resettable for SET_RESULT_FINISH_SPEC {}
