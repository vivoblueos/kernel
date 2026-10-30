#[doc = "Register `UNIT%s_LOAD` writer"]
pub type W = crate::W<UNIT_LOAD_SPEC>;
#[doc = "Field `LOAD` writer - timer unit0 sync enable signal"]
pub type LOAD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<UNIT_LOAD_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - timer unit0 sync enable signal"]
    #[inline(always)]
    pub fn load(&mut self) -> LOAD_W<'_, UNIT_LOAD_SPEC> {
        LOAD_W::new(self, 0)
    }
}
#[doc = "system timer unit%s conf sync register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`unit_load::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct UNIT_LOAD_SPEC;
impl crate::RegisterSpec for UNIT_LOAD_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`unit_load::W`](W) writer structure"]
impl crate::Writable for UNIT_LOAD_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets UNIT%s_LOAD to value 0"]
impl crate::Resettable for UNIT_LOAD_SPEC {}
