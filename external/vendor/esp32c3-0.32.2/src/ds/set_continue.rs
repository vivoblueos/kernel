#[doc = "Register `SET_CONTINUE` writer"]
pub type W = crate::W<SET_CONTINUE_SPEC>;
#[doc = "Field `SET_CONTINUE` writer - set this bit to continue DS operation."]
pub type SET_CONTINUE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SET_CONTINUE_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - set this bit to continue DS operation."]
    #[inline(always)]
    pub fn set_continue(&mut self) -> SET_CONTINUE_W<'_, SET_CONTINUE_SPEC> {
        SET_CONTINUE_W::new(self, 0)
    }
}
#[doc = "DS continue control register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`set_continue::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SET_CONTINUE_SPEC;
impl crate::RegisterSpec for SET_CONTINUE_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`set_continue::W`](W) writer structure"]
impl crate::Writable for SET_CONTINUE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SET_CONTINUE to value 0"]
impl crate::Resettable for SET_CONTINUE_SPEC {}
