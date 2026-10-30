#[doc = "Register `SET_INVALIDATE_JTAG` writer"]
pub type W = crate::W<SET_INVALIDATE_JTAG_SPEC>;
#[doc = "Field `SET_INVALIDATE_JTAG` writer - Clear result from hmac downstream JTAG."]
pub type SET_INVALIDATE_JTAG_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SET_INVALIDATE_JTAG_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Clear result from hmac downstream JTAG."]
    #[inline(always)]
    pub fn set_invalidate_jtag(&mut self) -> SET_INVALIDATE_JTAG_W<'_, SET_INVALIDATE_JTAG_SPEC> {
        SET_INVALIDATE_JTAG_W::new(self, 0)
    }
}
#[doc = "Invalidate register 0.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`set_invalidate_jtag::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SET_INVALIDATE_JTAG_SPEC;
impl crate::RegisterSpec for SET_INVALIDATE_JTAG_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`set_invalidate_jtag::W`](W) writer structure"]
impl crate::Writable for SET_INVALIDATE_JTAG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SET_INVALIDATE_JTAG to value 0"]
impl crate::Resettable for SET_INVALIDATE_JTAG_SPEC {}
