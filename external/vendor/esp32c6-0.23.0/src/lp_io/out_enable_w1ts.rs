#[doc = "Register `OUT_ENABLE_W1TS` writer"]
pub type W = crate::W<OUT_ENABLE_W1TS_SPEC>;
#[doc = "Field `ENABLE_W1TS` writer - set one time output data"]
pub type ENABLE_W1TS_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<OUT_ENABLE_W1TS_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bits 0:7 - set one time output data"]
    #[inline(always)]
    pub fn enable_w1ts(&mut self) -> ENABLE_W1TS_W<'_, OUT_ENABLE_W1TS_SPEC> {
        ENABLE_W1TS_W::new(self, 0)
    }
}
#[doc = "need des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_enable_w1ts::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OUT_ENABLE_W1TS_SPEC;
impl crate::RegisterSpec for OUT_ENABLE_W1TS_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`out_enable_w1ts::W`](W) writer structure"]
impl crate::Writable for OUT_ENABLE_W1TS_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets OUT_ENABLE_W1TS to value 0"]
impl crate::Resettable for OUT_ENABLE_W1TS_SPEC {}
