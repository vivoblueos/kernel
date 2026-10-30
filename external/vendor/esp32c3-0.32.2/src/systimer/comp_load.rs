#[doc = "Register `COMP%s_LOAD` writer"]
pub type W = crate::W<COMP_LOAD_SPEC>;
#[doc = "Field `LOAD` writer - timer comp0 load value"]
pub type LOAD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<COMP_LOAD_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - timer comp0 load value"]
    #[inline(always)]
    pub fn load(&mut self) -> LOAD_W<'_, COMP_LOAD_SPEC> {
        LOAD_W::new(self, 0)
    }
}
#[doc = "SYSTIMER_COMP%s_LOAD.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`comp_load::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct COMP_LOAD_SPEC;
impl crate::RegisterSpec for COMP_LOAD_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`comp_load::W`](W) writer structure"]
impl crate::Writable for COMP_LOAD_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets COMP%s_LOAD to value 0"]
impl crate::Resettable for COMP_LOAD_SPEC {}
