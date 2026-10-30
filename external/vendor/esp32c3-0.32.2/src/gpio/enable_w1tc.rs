#[doc = "Register `ENABLE_W1TC` writer"]
pub type W = crate::W<ENABLE_W1TC_SPEC>;
#[doc = "Field `ENABLE_W1TC` writer - GPIO output enable clear register for GPIO0-25"]
pub type ENABLE_W1TC_W<'a, REG> = crate::FieldWriter<'a, REG, 26, u32>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<ENABLE_W1TC_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bits 0:25 - GPIO output enable clear register for GPIO0-25"]
    #[inline(always)]
    pub fn enable_w1tc(&mut self) -> ENABLE_W1TC_W<'_, ENABLE_W1TC_SPEC> {
        ENABLE_W1TC_W::new(self, 0)
    }
}
#[doc = "GPIO output enable clear register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`enable_w1tc::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ENABLE_W1TC_SPEC;
impl crate::RegisterSpec for ENABLE_W1TC_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`enable_w1tc::W`](W) writer structure"]
impl crate::Writable for ENABLE_W1TC_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ENABLE_W1TC to value 0"]
impl crate::Resettable for ENABLE_W1TC_SPEC {}
